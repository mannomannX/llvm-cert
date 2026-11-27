## Vellvm Project Makefile (Clean MIT/LGPL-2.1 Library & Extraction Build)

ROCQDIR = rocq
PASSESDIR = ../../passes
VALIDATORDIR = ../../validator
EXTRACTDIR = ml/extracted

ROCQINCLUDES=$(foreach d, $(ROCQDIR), -R $(d) Vellvm) -Q $(PASSESDIR) CertPasses -Q $(VALIDATORDIR) CertValidator -R $(EXTRACTDIR) Extract
ROCQEXEC="$(ROCQBIN)rocq" top -q -w none $(ROCQINCLUDES) -batch -load-vernac-source
ROCQMAKEFILE="$(ROCQBIN)rocq" makefile

DUNE_PROFILE?=release

ROCQFILES_FRONTEND := Syntax/ShowAST Syntax/ReprAST Utils/ParserHelper Syntax/LLVMAst Syntax/AstLib
ROCQFILES_EXEC := $(ROCQFILES_FRONTEND) Semantics
FRONTEND_VOFILES := $(ROCQFILES_FRONTEND:%=rocq/%.vo)
EXEC_VOFILES := $(ROCQFILES_EXEC:%=rocq/%.vo)
PASS_VOFILES := $(PASSESDIR)/common/ItreeTactics.vo $(PASSESDIR)/Pipeline.vo $(PASSESDIR)/McfgExport.vo $(PASSESDIR)/ModuleMerge.vo
VALIDATOR_VOFILES := $(VALIDATORDIR)/common/Options.vo $(VALIDATORDIR)/common/Diag.vo $(VALIDATORDIR)/common/CoreTactics.vo $(VALIDATORDIR)/common/BvTactics.vo $(VALIDATORDIR)/common/IntBvTactics.vo $(VALIDATORDIR)/common/EouTactics.vo $(VALIDATORDIR)/LratCore.vo $(VALIDATORDIR)/AigGates.vo $(VALIDATORDIR)/AigArith.vo $(VALIDATORDIR)/AigLrat.vo $(VALIDATORDIR)/CertFormatAst.vo $(VALIDATORDIR)/CertFormatParse.vo $(VALIDATORDIR)/CertFormatGates.vo $(VALIDATORDIR)/CertFormat.vo $(VALIDATORDIR)/AlgRulesEval.vo $(VALIDATORDIR)/AlgRulesNormBinop.vo $(VALIDATORDIR)/AlgRulesNormRefines.vo $(VALIDATORDIR)/AlgRules.vo $(VALIDATORDIR)/CfgDag.vo $(VALIDATORDIR)/CertValOpenWorld.vo $(VALIDATORDIR)/CertValExpReify.vo $(VALIDATORDIR)/CertValCfgDag.vo $(VALIDATORDIR)/CertValCfgSum.vo $(VALIDATORDIR)/CertValUbCheck.vo $(VALIDATORDIR)/CertValPathCheck.vo $(VALIDATORDIR)/CertValLoop.vo $(VALIDATORDIR)/CertValProto.vo $(VALIDATORDIR)/CertValidator.vo $(VALIDATORDIR)/Elf64Spec.vo $(VALIDATORDIR)/McFrameMem.vo $(VALIDATORDIR)/McIsaCommon.vo $(VALIDATORDIR)/Rv64Decode.vo $(VALIDATORDIR)/Rv64ExecSym.vo $(VALIDATORDIR)/Rv64DagProof.vo $(VALIDATORDIR)/Rv64SymOracle.vo $(VALIDATORDIR)/Rv64LoopSeg.vo $(VALIDATORDIR)/Rv64Sem.vo $(VALIDATORDIR)/A64Decode.vo $(VALIDATORDIR)/A64ExecSym.vo $(VALIDATORDIR)/A64DagProof.vo $(VALIDATORDIR)/A64SymOracle.vo $(VALIDATORDIR)/A64LoopSeg.vo $(VALIDATORDIR)/A64CoreSem.vo $(VALIDATORDIR)/McFormat.vo $(VALIDATORDIR)/McOblDischarger.vo $(VALIDATORDIR)/McLoopIrSpec.vo $(VALIDATORDIR)/McLoopCheck.vo $(VALIDATORDIR)/McLoop.vo $(VALIDATORDIR)/McCallSpec.vo $(VALIDATORDIR)/McCallMcWitness.vo $(VALIDATORDIR)/McCallIrExec.vo $(VALIDATORDIR)/McCall.vo $(VALIDATORDIR)/McExprRewrite.vo $(VALIDATORDIR)/McValidator.vo $(VALIDATORDIR)/CheckAssumptions.vo

.DEFAULT_GOAL := all

RocqMakefile: _RocqProject
	$(ROCQMAKEFILE) -f _RocqProject -o RocqMakefile

.PHONY: all
all:
	$(MAKE) rocq
	$(MAKE) extracted
	dune build --profile $(DUNE_PROFILE)

.PHONY: rocq
rocq: real-all

.PHONY: extracted
extracted: $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: $(EXEC_VOFILES) $(PASS_VOFILES) $(VALIDATOR_VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(ROCQEXEC) $(EXTRACTDIR)/Extract.v
	@echo "Post-processing extraction: unbox the itree node wrapper"
	perl -i -pe 's/^(\| Coq_go of .* itreeF)$$/$$1 [\@\@unboxed]/' $(EXTRACTDIR)/ITreeDefinition.ml $(EXTRACTDIR)/ITreeDefinition.mli
	touch $(EXTRACTDIR)/STAMP

.PHONY: clean
clean: extractedclean clean-rocqmakefile
	rm -rf output
	find rocq $(PASSESDIR) $(VALIDATORDIR) -name ".*.aux" -delete
	dune clean

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli $(EXTRACTDIR)/\#* $(EXTRACTDIR)/.!*

.PHONY: clean-rocqmakefile
clean-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile clean

$(EXTRACTDIR)/FRONTEND_STAMP: $(FRONTEND_VOFILES) $(EXTRACTDIR)/ExtractFrontend.v
	@echo "Extracting Frontend"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(ROCQEXEC) $(EXTRACTDIR)/ExtractFrontend.v
	touch $(EXTRACTDIR)/FRONTEND_STAMP
	rm -f $(EXTRACTDIR)/STAMP

.PHONY: opam
opam:
	opam install -y --verbose --deps-only ..

.PHONY: print-includes
print-includes:
	@echo $(ROCQINCLUDES)

Makefile _RocqProject \
$(EXTRACTDIR)/Extract.v $(EXTRACTDIR)/ExtractFrontend.v \
ml/dune ml/extracted/dune ml/IO.ml: ;

.PHONY: rocqmakefile-exec
rocqmakefile-exec:
	+$(MAKE) --no-print-directory -f RocqMakefile $(EXEC_VOFILES) $(PASS_VOFILES) $(VALIDATOR_VOFILES)

.PHONY: rocqmakefile-frontend
rocqmakefile-frontend:
	+$(MAKE) --no-print-directory -f RocqMakefile $(FRONTEND_VOFILES)

$(FRONTEND_VOFILES): RocqMakefile rocqmakefile-frontend ;
$(filter-out $(FRONTEND_VOFILES),$(EXEC_VOFILES)) $(PASS_VOFILES) $(VALIDATOR_VOFILES): RocqMakefile rocqmakefile-exec ;

.PHONY: invoke-rocqmakefile
invoke-rocqmakefile: RocqMakefile

%: invoke-rocqmakefile
	+$(MAKE) --no-print-directory -f RocqMakefile $@
