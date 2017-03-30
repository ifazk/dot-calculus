COQC=coqc

FILES=Safety.v

DEFS= Definitions.v
DEFSOBJECTS=$(DEFS:.v=.vo)

PROOFS= \
      Weakening.v \
      Wellformed_store.v \
      Extra_rec.v \
      Substitution.v \
      Some_lemmas.v \
      Narrowing.v \
      Has_member.v \
      Tight_bound_completeness.v \
      Misc.v \
      Precise_flow.v \
      Inductive_opens.v \
      Good_types.v \
      General_to_tight.v \
      Canonical_forms1.v \
      Canonical_forms2.v
PROOFOBJECTS=$(PROOFS:.v=.vo)


OBJECTS=$(FILES:.v=.vo)

TLCDIR=../../../ln/tlc/
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

all: $(OBJECTS)

$(LIBLN):
	cd $(TLCDIR) && make

%.vo:%.v $(LIBLN)
	$(COQC) -R $(TLCDIR) $(TLCNAME) $<

.PHONY:clean

COMPILEFILES=$(DEFS) $(PROOFS) $(FILES)
CLEANFILES=$(COMPILEFILES:.v=.vo) $(COMPILEFILES:%.v=.%.vo.aux) $(COMPILEFILES:.v=.glob)

clean::
	rm -f $(CLEANFILES)

# Extra deps
$(PROOFOBJECTS): Definitions.vo
Substitution.vo: Weakening.vo
Some_lemmas.vo: Weakening.vo Wellformed_store.vo
Narrowing.vo: Weakening.vo
Has_member.vo: Some_lemmas.vo
Tight_bound_completeness.vo: Some_lemmas.vo Has_member.vo
Safety.vo: Definitions.vo \
           Weakening.vo \
           Wellformed_store.vo \
           Substitution.vo \
           Narrowing.vo \
           Misc.vo \
           Canonical_forms1.vo \
           Canonical_forms2.vo
Inductive_opens.vo: Definitions.vo
Precise_flow.vo: Definitions.vo Inductive_opens.vo Wellformed_store.vo Some_lemmas.vo
Good_types.vo: Definitions.vo \
               Inductive_opens.vo \
               Wellformed_store.vo \
               Has_member.vo \
               Some_lemmas.vo \
               Precise_flow.vo \
               Tight_bound_completeness.vo
Tight_possible_types.vo: Precise_flow.vo \
                         Good_types.vo
General_to_tight.vo: Wellformed_store.vo \
                     Narrowing.vo \
                     Good_types.vo \
                     Some_lemmas.vo \
                     Tight_possible_types.vo
Canonical_forms1.vo: Definitions.vo \
                     Wellformed_store.vo \
                     Some_lemmas.vo \
                     Narrowing.vo \
                     Tight_possible_types.vo \
                     Good_types.vo \
                     General_to_tight.vo \
                     Extra_rec.vo
Canonical_forms2.vo: Definitions.vo \
                     Weakening.vo \
                     Wellformed_store.vo \
                     Substitution.vo \
                     Some_lemmas.vo \
                     Has_member.vo \
                     Tight_bound_completeness.vo \
                     Precise_flow.vo \
                     Good_types.vo \
                     General_to_tight.vo
