## Vellvm Project Makefile (Clean MIT/LGPL-2.1 Library & Extraction Build)

ROCQDIR = rocq
EXTRACTDIR = ml/extracted

ROCQINCLUDES=$(foreach d, $(ROCQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract
ROCQEXEC="$(ROCQBIN)rocq" top -q -w none $(ROCQINCLUDES) -batch -load-vernac-source
ROCQMAKEFILE="$(ROCQBIN)rocq" makefile

DUNE_PROFILE?=release

ROCQFILES_FRONTEND := Syntax/ShowAST Syntax/ReprAST Utils/ParserHelper Syntax/LLVMAst Syntax/AstLib
ROCQFILES_EXEC := $(ROCQFILES_FRONTEND) Semantics
FRONTEND_VOFILES := $(ROCQFILES_FRONTEND:%=rocq/%.vo)
EXEC_VOFILES := $(ROCQFILES_EXEC:%=rocq/%.vo)

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

$(EXTRACTDIR)/STAMP: $(EXEC_VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	$(ROCQEXEC) $(EXTRACTDIR)/Extract.v
	@echo "Post-processing extraction: unbox the itree node wrapper"
	perl -i -pe 's/^(\| Coq_go of .* itreeF)$$/$$1 [\@\@unboxed]/' $(EXTRACTDIR)/ITreeDefinition.ml $(EXTRACTDIR)/ITreeDefinition.mli
	touch $(EXTRACTDIR)/STAMP

.PHONY: clean
clean: extractedclean clean-rocqmakefile
	rm -rf output
	find rocq -name ".*.aux" -delete
	dune clean

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli $(EXTRACTDIR)/\#* $(EXTRACTDIR)/.!*

.PHONY: clean-rocqmakefile
clean-rocqmakefile: RocqMakefile
	$(MAKE) -j --no-print-directory -f RocqMakefile clean

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
	+$(MAKE) -j --no-print-directory -f RocqMakefile $(EXEC_VOFILES)

.PHONY: rocqmakefile-frontend
rocqmakefile-frontend:
	+$(MAKE) -j --no-print-directory -f RocqMakefile $(FRONTEND_VOFILES)

$(FRONTEND_VOFILES): RocqMakefile rocqmakefile-frontend ;
$(filter-out $(FRONTEND_VOFILES),$(EXEC_VOFILES)): RocqMakefile rocqmakefile-exec ;

.PHONY: invoke-rocqmakefile
invoke-rocqmakefile: RocqMakefile

%: invoke-rocqmakefile
	+$(MAKE) -j --no-print-directory -f RocqMakefile $@
