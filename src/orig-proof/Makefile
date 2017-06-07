FILES=Dot_proofs_safety.v
OBJECTS=$(FILES:.v=.vo)

PROOFS= \
    Dot_definitions.v \
    Dot_proofs_extra_rec.v \
    Dot_proofs_has_member.v \
    Dot_proofs_misc_inversions.v \
    Dot_proofs_misc.v \
    Dot_proofs_narrowing.v \
    Dot_proofs_possible_types.v \
    Dot_proofs_safety.v \
    Dot_proofs_some_lemmas.v \
    Dot_proofs_substitution.v \
    Dot_proofs_tight_bound_completeness.v \
    Dot_proofs_weakening.v \
    Dot_proofs_wellformed_store.v
PROOFOBJECTS=$(PROOFS:.v=.vo)

TLCDIR=../../lib/tlc/
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME) -R . \"\"
COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq

##############
# Main Rules #
##############

.PHONY: all clean
all:
	$(MAKE) -f $(PROOFMAKEFILE) $(OBJECTS)

clean:
	$(MAKE) -f $(PROOFMAKEFILE) cleanall

%.vo:
	$(MAKE) -f $(PROOFMAKEFILE) $@

all clean: $(PROOFMAKEFILE)
%vo: $(PROOFMAKEFILE)

all: $(LIBLN)
%vo: $(LIBLN)

##############
# Main Rules #
##############

.PHONY: ide
ide: _CoqProject

########################
# Library Dependencies #
########################

$(LIBLN):
	cd $(TLCDIR) && make

###################
# Forced Rebuilds #
###################

.PHONY: init
init: $(PROOFMAKEFILE) _CoqProject

$(PROOFMAKEFILE): .FORCE
	@$(COQMAKEFILE) $(COQINCLUDE) -install none $(PROOFS) > $@

_CoqProject: .FORCE
	@echo $(COQINCLUDE) > $@

.FORCE:
