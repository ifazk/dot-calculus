FILES=Safety.v
OBJECTS=$(FILES:.v=.vo)

PROOFS= \
    Definitions.v \
    Wellformed_store.v \
    Weakening.v \
    Helper_lemmas.v \
    Precise_types.v \
    Invertible_typing.v \
    Substitution.v \
    Narrowing.v \
    General_to_tight.v \
    Canonical_forms1.v \
    Canonical_forms2.v \
    Safety.v
PROOFOBJECTS=$(PROOFS:.v=.vo)

TLCDIR=../lib/tlc/
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME) -R . \"\"
COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq

##############
# Main Rules #
##############

.PHONY: all doc proofs clean
all: proofs doc

proofs:
	$(MAKE) -f $(PROOFMAKEFILE) $(OBJECTS)

clean:
	$(MAKE) -f $(PROOFMAKEFILE) cleanall
	$(RM) ../doc/*.html
	$(RM) ../doc/*.css

doc:
	$(MAKE) -f $(PROOFMAKEFILE) html

%.vo:
	$(MAKE) -f $(PROOFMAKEFILE) $@

all doc clean: $(PROOFMAKEFILE)
%vo: $(PROOFMAKEFILE)

all: $(LIBLN)
doc: $(LIBLN)
proofs: $(LIBLN)
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

graph.png: $(PROOFS)
	coqdep -dumpgraph graph.dot *.v
	dot -Tpng graph.dot > graph.png

#################
# Documentation #
#################

EXTRA_DIR:=../doc/assets
COQDOCFLAGS:= \
  --no-externals \
  --toc --toc-depth 2 --html \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
