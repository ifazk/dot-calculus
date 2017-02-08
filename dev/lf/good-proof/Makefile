COQC=coqc

FILES=Dot_proofs_safety.v

DEFS= Dot_definitions.v
DEFSOBJECTS=$(DEFS:.v=.vo)

PROOFS= \
      Dot_proofs_weakening.v \
      Dot_proofs_wellformed_store.v \
      Dot_proofs_extra_rec.v \
      Dot_proofs_substitution.v \
      Dot_proofs_some_lemmas.v \
      Dot_proofs_narrowing.v \
      Dot_proofs_has_member.v \
      Dot_proofs_tight_bound_completeness.v \
      Dot_proofs_misc_inversions.v \
      Dot_proofs_possible_types.v \
      Dot_proofs_misc.v
PROOFOBJECTS=$(PROOFS:.v=.vo)


OBJECTS=$(FILES:.v=.vo)

INCLUDESDIR=../../../ln/tlc/
LIBLN=$(INCLUDESDIR)/LibLN.vo

all: $(OBJECTS)

$(LIBLN):
	cd $(INCLUDESDIR) && make

%.vo:%.v $(LIBLN)
	$(COQC) -I $(INCLUDESDIR) $<

.PHONY:clean

clean::
	rm -f $(DEFSOBJECTS)
	rm -f $(DEFS:.v=.glob)
	rm -f $(PROOFOBJECTS)
	rm -f $(PROOFS:.v=.glob)
	rm -f $(OBJECTS)
	rm -f $(FILES:.v=.glob)

# Extra deps
$(PROOFOBJECTS): Dot_definitions.vo
Dot_proofs_substitution.vo: Dot_proofs_weakening.vo
Dot_proofs_some_lemmas.vo: Dot_proofs_weakening.vo Dot_proofs_wellformed_store.vo
Dot_proofs_narrowing.vo: Dot_proofs_weakening.vo
Dot_proofs_has_member.vo: Dot_proofs_some_lemmas.vo
Dot_proofs_tight_bound_completeness.vo: Dot_proofs_some_lemmas.vo Dot_proofs_has_member.vo
Dot_proofs_misc_inversions.vo: Dot_proofs_some_lemmas.vo
Dot_proofs_possible_types.vo: Dot_proofs_weakening.vo \
			      Dot_proofs_wellformed_store.vo \
                              Dot_proofs_substitution.vo \
                              Dot_proofs_some_lemmas.vo \
                              Dot_proofs_narrowing.vo \
                              Dot_proofs_has_member.vo \
                              Dot_proofs_tight_bound_completeness.vo \
                              Dot_proofs_misc_inversions.vo
Dot_proofs_safety.vo: Dot_definitions.vo \
                      Dot_proofs_weakening.vo \
                      Dot_proofs_wellformed_store.vo \
                      Dot_proofs_substitution.vo \
                      Dot_proofs_narrowing.vo \
                      Dot_proofs_possible_types.vo \
                      Dot_proofs_misc.vo
