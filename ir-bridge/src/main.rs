use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use ir_bridge::{
    BridgeError, FastPathEligibility, ModuleManifest, SliceRole, check_fast_path_eligibility,
    merge_module, sanitize_for_vellvm, split_module_for_vellvm,
};

fn main() -> ExitCode {
    match run_cli() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("ir-bridge error: {err}");
            ExitCode::FAILURE
        }
    }
}

fn run_cli() -> Result<(), BridgeError> {
    let args: Vec<String> = env::args().skip(1).collect();
    let Some(subcmd) = args.first().map(String::as_str) else {
        print_usage();
        return Ok(());
    };
    let rest = args.get(1..).unwrap_or(&[]);

    match subcmd {
        "to-vellvm" => cmd_to_vellvm(rest),
        "check-eligibility" => cmd_check_eligibility(rest),
        "split" => cmd_split(rest),
        "merge" => cmd_merge(rest),
        "--help" | "-h" | "help" => {
            print_usage();
            Ok(())
        }
        other => Err(BridgeError::MalformedModule {
            detail: format!("unknown subcommand `{other}` (run `ir-bridge --help`)"),
        }),
    }
}

fn cmd_to_vellvm(args: &[String]) -> Result<(), BridgeError> {
    let mut input: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut role = SliceRole::Source;

    let mut i = 0_usize;
    while let Some(arg) = args.get(i) {
        match arg.as_str() {
            "-o" | "--output" => {
                let val = args
                    .get(i + 1)
                    .ok_or_else(|| BridgeError::MalformedModule {
                        detail: "missing path after `-o`".to_owned(),
                    })?;
                output = Some(PathBuf::from(val));
                i += 2;
            }
            "--role" => {
                let val = args
                    .get(i + 1)
                    .ok_or_else(|| BridgeError::MalformedModule {
                        detail: "missing value after `--role` (`source` or `target-fast`)"
                            .to_owned(),
                    })?;
                role = match val.as_str() {
                    "source" => SliceRole::Source,
                    "target-fast" => SliceRole::TargetFastPath,
                    other => {
                        return Err(BridgeError::MalformedModule {
                            detail: format!(
                                "invalid `--role {other}` (expected `source` or `target-fast`)"
                            ),
                        });
                    }
                };
                i += 2;
            }
            path_str => {
                input = Some(PathBuf::from(path_str));
                i += 1;
            }
        }
    }

    let in_path = input.ok_or_else(|| BridgeError::MalformedModule {
        detail: "usage: ir-bridge to-vellvm <input.ll> -o <output.ll> [--role source|target-fast]"
            .to_owned(),
    })?;
    let raw = read_utf8(&in_path)?;
    let sanitized = sanitize_for_vellvm(&raw, role)?;

    if let Some(out_path) = output {
        write_utf8(&out_path, &sanitized)?;
    } else {
        print!("{sanitized}");
    }
    Ok(())
}

fn cmd_check_eligibility(args: &[String]) -> Result<(), BridgeError> {
    let in_path = args
        .first()
        .map(PathBuf::from)
        .ok_or_else(|| BridgeError::MalformedModule {
            detail: "usage: ir-bridge check-eligibility <opt_fast.ll>".to_owned(),
        })?;
    let raw = read_utf8(&in_path)?;
    match check_fast_path_eligibility(&raw) {
        FastPathEligibility::Eligible => {
            println!("ELIGIBLE");
            Ok(())
        }
        FastPathEligibility::FallbackRequired { reasons } => {
            Err(BridgeError::FastPathIneligible { reasons })
        }
    }
}

fn cmd_split(args: &[String]) -> Result<(), BridgeError> {
    let mut input: Option<PathBuf> = None;
    let mut out_dir: Option<PathBuf> = None;

    let mut i = 0_usize;
    while let Some(arg) = args.get(i) {
        match arg.as_str() {
            "--out-dir" | "-d" => {
                let val = args
                    .get(i + 1)
                    .ok_or_else(|| BridgeError::MalformedModule {
                        detail: "missing directory after `--out-dir`".to_owned(),
                    })?;
                out_dir = Some(PathBuf::from(val));
                i += 2;
            }
            path_str => {
                input = Some(PathBuf::from(path_str));
                i += 1;
            }
        }
    }

    let in_path = input.ok_or_else(|| BridgeError::MalformedModule {
        detail: "usage: ir-bridge split <module.ll> --out-dir <dir>".to_owned(),
    })?;
    let dir = out_dir.ok_or_else(|| BridgeError::MalformedModule {
        detail: "usage: ir-bridge split <module.ll> --out-dir <dir>".to_owned(),
    })?;

    fs::create_dir_all(&dir).map_err(|source| BridgeError::Io {
        path: dir.clone(),
        source,
    })?;

    let raw = read_utf8(&in_path)?;
    let split = split_module_for_vellvm(&raw)?;

    let manifest_path = dir.join("manifest.json");
    let manifest_json =
        serde_json::to_string_pretty(&split.manifest).map_err(BridgeError::ManifestJson)?;
    write_utf8(&manifest_path, &manifest_json)?;

    for (fn_name, slice_ir) in &split.slices {
        let safe_stem = sanitize_filename(fn_name);
        let slice_path = dir.join(format!("{safe_stem}.input.ll"));
        write_utf8(&slice_path, slice_ir)?;
    }
    Ok(())
}

fn cmd_merge(args: &[String]) -> Result<(), BridgeError> {
    let mut manifest_path: Option<PathBuf> = None;
    let mut slices_dir: Option<PathBuf> = None;
    let mut out_path: Option<PathBuf> = None;
    let mut verify_tool: Option<PathBuf> = None;

    let mut i = 0_usize;
    while let Some(arg) = args.get(i) {
        match arg.as_str() {
            "--manifest" => {
                let val = args
                    .get(i + 1)
                    .ok_or_else(|| BridgeError::MalformedModule {
                        detail: "missing path after `--manifest`".to_owned(),
                    })?;
                manifest_path = Some(PathBuf::from(val));
                i += 2;
            }
            "--slices-dir" => {
                let val = args
                    .get(i + 1)
                    .ok_or_else(|| BridgeError::MalformedModule {
                        detail: "missing directory after `--slices-dir`".to_owned(),
                    })?;
                slices_dir = Some(PathBuf::from(val));
                i += 2;
            }
            "-o" | "--output" => {
                let val = args
                    .get(i + 1)
                    .ok_or_else(|| BridgeError::MalformedModule {
                        detail: "missing path after `-o`".to_owned(),
                    })?;
                out_path = Some(PathBuf::from(val));
                i += 2;
            }
            "--verify-with" => {
                let val = args
                    .get(i + 1)
                    .ok_or_else(|| BridgeError::MalformedModule {
                        detail: "missing `opt` path after `--verify-with`".to_owned(),
                    })?;
                verify_tool = Some(PathBuf::from(val));
                i += 2;
            }
            other => {
                return Err(BridgeError::MalformedModule {
                    detail: format!("unexpected argument `{other}` in `merge`"),
                });
            }
        }
    }

    let mf_path = manifest_path.ok_or_else(|| BridgeError::MalformedModule {
        detail:
            "usage: ir-bridge merge --manifest <manifest.json> --slices-dir <dir> -o <merged.ll>"
                .to_owned(),
    })?;
    let s_dir = slices_dir.ok_or_else(|| BridgeError::MalformedModule {
        detail:
            "usage: ir-bridge merge --manifest <manifest.json> --slices-dir <dir> -o <merged.ll>"
                .to_owned(),
    })?;
    let target_out = out_path.ok_or_else(|| BridgeError::MalformedModule {
        detail:
            "usage: ir-bridge merge --manifest <manifest.json> --slices-dir <dir> -o <merged.ll>"
                .to_owned(),
    })?;

    let mf_text = read_utf8(&mf_path)?;
    let manifest: ModuleManifest =
        serde_json::from_str(&mf_text).map_err(BridgeError::ManifestJson)?;

    let mut verified_slices = BTreeMap::new();
    for f in &manifest.functions {
        let stem = sanitize_filename(&f.name);
        let candidate_paths = [
            s_dir.join(format!("{stem}.verified.ll")),
            s_dir.join(format!("{stem}.opt_fast.ll")),
            s_dir.join(format!("{stem}.opt_safe.ll")),
            s_dir.join(format!("{stem}.input.ll")),
        ];
        let found = candidate_paths.iter().find(|p| p.is_file());
        let Some(p) = found else {
            return Err(BridgeError::MissingVerifiedSlice {
                function_name: f.name.clone(),
            });
        };
        verified_slices.insert(f.name.clone(), read_utf8(p)?);
    }

    let merged = merge_module(&manifest, &verified_slices)?;
    write_utf8(&target_out, &merged)?;

    if let Some(opt_bin) = verify_tool {
        let status = Command::new(&opt_bin)
            .arg("-passes=verify")
            .arg("-disable-output")
            .arg(&target_out)
            .output()
            .map_err(|source| BridgeError::Io {
                path: opt_bin.clone(),
                source,
            })?;
        if !status.status.success() {
            return Err(BridgeError::VerificationToolFailed {
                tool: opt_bin.display().to_string(),
                stderr: String::from_utf8_lossy(&status.stderr).into_owned(),
            });
        }
    }

    Ok(())
}

fn sanitize_filename(sym: &str) -> String {
    sym.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.') {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn read_utf8(path: &Path) -> Result<String, BridgeError> {
    fs::read_to_string(path).map_err(|source| BridgeError::Io {
        path: path.to_path_buf(),
        source,
    })
}

fn write_utf8(path: &Path, content: &str) -> Result<(), BridgeError> {
    fs::write(path, content).map_err(|source| BridgeError::Io {
        path: path.to_path_buf(),
        source,
    })
}

fn print_usage() {
    println!(
        "\
ir-bridge — LLVMCert High-Assurance LLVM 23.1.5 <-> Vellvm 3.0 Bridge

USAGE:
  ir-bridge to-vellvm <input.ll> [-o <output.ll>] [--role source|target-fast]
  ir-bridge check-eligibility <opt_fast.ll>
  ir-bridge split <module.ll> --out-dir <dir>
  ir-bridge merge --manifest <manifest.json> --slices-dir <dir> -o <merged.ll> [--verify-with <opt>]"
    );
}
