// Copyright (c) 2026 LLVMCert Contributors. All rights reserved.
// Licensed under the LLVMCert Non-Commercial Evaluation & Research License
// or a separate LLVMCert Commercial Software License Agreement.
// See /LICENSE in the repository root for details.
//
// Persistent batch symbolic executor built on top of rems-project/isla
// (`BSD-2-Clause`). Loads a compiled Sail `.ir` snapshot once and streams
// simplified per-instruction symbolic execution traces over stdin/stdout.

use crossbeam::queue::SegQueue;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::convert::TryInto;
use std::io::{self, BufRead, Write};
use std::process::exit;
use std::sync::Arc;

use isla_lib::bitvector::{b129::B129, BV};
use isla_lib::executor;
use isla_lib::executor::{LocalFrame, StopAction, StopConditions, TaskId, TaskState};
use isla_lib::init::initialize_architecture;
use isla_lib::ir::*;
use isla_lib::memory::Memory;
use isla_lib::register::Register;
use isla_lib::simplify;
use isla_lib::simplify::WriteOpts;
use isla_lib::smt;
use isla_lib::smt::{Checkpoint, Event, Solver};
use isla_lib::zencode;

#[path = "../opts.rs"]
mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_batch_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn hex_bytes(s: &str) -> Result<Vec<u8>, std::num::ParseIntError> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect()
}

fn opcode_bytes<B: BV>(opcode: Vec<u8>, little_endian: bool) -> B {
    if opcode.len() == 2 {
        let arr: Box<[u8; 2]> = opcode.into_boxed_slice().try_into().unwrap();
        B::from_u16(if little_endian {
            u16::from_le_bytes(*arr)
        } else {
            u16::from_be_bytes(*arr)
        })
    } else if opcode.len() == 4 {
        let arr: Box<[u8; 4]> = opcode.into_boxed_slice().try_into().unwrap();
        B::from_u32(if little_endian {
            u32::from_le_bytes(*arr)
        } else {
            u32::from_be_bytes(*arr)
        })
    } else {
        B::from_bytes(&opcode)
    }
}

fn isla_batch_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optopt(
        "e",
        "endianness",
        "instruction encoding endianness (default: little)",
        "big/little",
    );
    opts.optopt(
        "f",
        "function",
        "use a custom footprint function",
        "<identifier>",
    );
    opts.optmulti(
        "k",
        "kill-at",
        "stop executions early and discard if they reach this function",
        "<function name>",
    );
    opts.optmulti(
        "",
        "stop-at",
        "stop executions early and keep trace if they reach this function",
        "<function name>",
    );
    opts.optflag("", "pessimistic", "fail on any assertion that is not necessarily true");
    opts.optopt("", "timeout", "Add a timeout (in seconds)", "<n>");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse(&mut hasher, &opts);
    let CommonOpts {
        num_threads,
        mut arch,
        symtab,
        type_info,
        isa_config,
        ..
    } = opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let assertion_mode = if matches.opt_present("pessimistic") {
        AssertionMode::Pessimistic
    } else {
        AssertionMode::Optimistic
    };
    let use_model_reg_init = !matches.opt_present("no-model-reg-init");
    let iarch = initialize_architecture(
        &mut arch,
        symtab,
        type_info,
        &isa_config,
        assertion_mode,
        use_model_reg_init,
    );
    let regs = &iarch.regs;
    let lets = &iarch.lets;
    let shared_state = &&iarch.shared_state;

    let little_endian = match matches.opt_str("endianness").as_deref() {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be either `big` or `little`");
            return 1;
        }
    };
    let timeout: Option<u64> = match matches.opt_get("timeout") {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Failed to parse --timeout: {}", e);
            return 1;
        }
    };

    let kill_conditions = StopConditions::parse(
        matches.opt_strs("kill-at"),
        shared_state,
        StopAction::Kill,
    );
    let abstract_conditions = StopConditions::parse(
        matches.opt_strs("stop-at"),
        shared_state,
        StopAction::Abstract,
    );
    let stop_conditions = kill_conditions.union(&abstract_conditions);

    let footprint_function = match matches.opt_str("function") {
        Some(id) => zencode::encode(&id),
        None => "zisla_footprint".to_string(),
    };
    let function_id = shared_state.symtab.lookup(&footprint_function);
    let (args, ret_ty, instrs) = shared_state
        .functions
        .get(&function_id)
        .expect("footprint function missing in architecture IR");

    let base_checkpoint = {
        let solver_cfg = smt::Config::new();
        let solver_ctx = smt::Context::new(solver_cfg);
        let mut solver = Solver::<B129>::from_checkpoint(&solver_ctx, Checkpoint::new());
        let mut sorted_regs: Vec<(&Name, &Register<B129>)> = regs.iter().collect();
        sorted_regs.sort_by_key(|(name, _)| *name);
        for (name, reg) in sorted_regs {
            if let Some(value) = reg.read_last_if_initialized() {
                solver.add_event(Event::AssumeReg(*name, vec![], value.clone()));
            }
        }
        smt::checkpoint(&mut solver)
    };

    let write_opts = WriteOpts {
        define_enum: false,
        hide_uninteresting: true,
        ..WriteOpts::default()
    };

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = stdout.lock();

    for line_res in stdin.lock().lines() {
        let line = match line_res {
            Ok(l) => l,
            Err(e) => {
                eprintln!("stdin error: {}", e);
                return 1;
            }
        };
        let tok = line.trim();
        if tok.is_empty() {
            continue;
        }
        if tok == "PING" {
            writeln!(out, "PONG").unwrap();
            out.flush().unwrap();
            continue;
        }
        if tok == "QUIT" {
            break;
        }
        let bytes = match hex_bytes(tok) {
            Ok(b) if b.len() == 2 || b.len() == 4 => b,
            Ok(b) => {
                writeln!(out, "BEGIN {} 0 1", tok).unwrap();
                writeln!(out, "ERROR invalid opcode byte length {}", b.len()).unwrap();
                writeln!(out, "END {}", tok).unwrap();
                out.flush().unwrap();
                continue;
            }
            Err(e) => {
                writeln!(out, "BEGIN {} 0 1", tok).unwrap();
                writeln!(out, "ERROR invalid hex {}: {}", tok, e).unwrap();
                writeln!(out, "END {}", tok).unwrap();
                out.flush().unwrap();
                continue;
            }
        };
        let bv = opcode_bytes::<B129>(bytes, little_endian);
        let opcode_val = Val::Bits(bv);

        let memory = Memory::new();
        let reset_registers = HashMap::new();
        let task_state = TaskState::new().with_reset_registers(reset_registers);
        let mut task = LocalFrame::new(
            function_id,
            args,
            ret_ty,
            Some(&[opcode_val]),
            instrs,
        )
        .add_lets(lets)
        .add_regs(regs)
        .set_memory(memory)
        .task_with_checkpoint(TaskId::fresh(), &task_state, base_checkpoint.clone());
        task.set_stop_conditions(&stop_conditions);

        let queue = Arc::new(SegQueue::new());
        executor::start_multi(
            num_threads,
            timeout,
            vec![task],
            shared_state,
            queue.clone(),
            &executor::trace_collector,
        );

        let mut traces: Vec<Vec<u8>> = Vec::new();
        let mut errors: Vec<String> = Vec::new();
        loop {
            match queue.pop() {
                Some(Ok((_, mut events))) => {
                    simplify::hide_initialization(&mut events);
                    simplify::remove_extra_register_fields(&mut events);
                    simplify::remove_repeated_register_reads(&mut events);
                    simplify::remove_unused_register_assumptions(&mut events);
                    simplify::remove_unused(&mut events);
                    simplify::propagate_forwards_used_once(&mut events);
                    simplify::commute_extract(&mut events);
                    simplify::eval(&mut events);
                    let events: Vec<Event<B129>> = events.drain(..).rev().collect();
                    let mut buf: Vec<u8> = Vec::new();
                    simplify::write_events_with_opts(&mut buf, &events, shared_state, &write_opts)
                        .unwrap();
                    traces.push(buf);
                }
                Some(Err(err)) => {
                    errors.push(err.to_string().replace('\n', " "));
                }
                None => break,
            }
        }

        writeln!(out, "BEGIN {} {} {}", tok, traces.len(), errors.len()).unwrap();
        for err in &errors {
            writeln!(out, "ERROR {}", err).unwrap();
        }
        for (idx, tr) in traces.iter().enumerate() {
            writeln!(out, "TRACE {} {}", idx, tr.len()).unwrap();
            out.write_all(tr).unwrap();
            writeln!(out).unwrap();
        }
        writeln!(out, "END {}", tok).unwrap();
        out.flush().unwrap();
    }
    0
}
