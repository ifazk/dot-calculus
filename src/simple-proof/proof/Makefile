FILES=Safety.v
OBJECTS=$(FILES:.v=.vo)

TLCDIR=../lib/tlc
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME) -R . \"\"
COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq
PROOFS=$(wildcard *.v)

##############
# Main Rules #
##############

.PHONY: all doc proofs clean cleanall
all: proofs doc

proofs: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) $(OBJECTS)

clean: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) cleanall

cleanall:: clean
cleanall::
	-rm .*.aux
	-rm *.vo
	-rm *.glob
	-rm *.v.d
	-rm $(PROOFMAKEFILE)

doc: ../doc/toc.html

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

.PHONY: $(PROOFMAKEFILE)

$(PROOFMAKEFILE):
	$(COQMAKEFILE) $(COQINCLUDE) -install none -o $(PROOFMAKEFILE) $(PROOFS)
	sed -i -e "s|mkdir -p html|mkdir -p ../doc|g" $(PROOFMAKEFILE)
	sed -i -e "s|-d html|-d ../doc|g" $(PROOFMAKEFILE)
	sed -i -e "s|rm -rf html|rm -rf ../doc/*.html|g" $(PROOFMAKEFILE)

graph.png: $(PROOFS)
	coqdep -dumpgraph graph.dot *.v
	dot -Tpng graph.dot > graph.png

#################
# Documentation #
#################

DOCDEP=$(shell coqdep -sort $(FILES) | sed -e "s|\\.vo|\\.v|g")

../doc/toc.html: $(DOCDEP)
	$(MAKE) -f $(PROOFMAKEFILE) VFILES="$(DOCDEP)" html

EXTRA_DIR:=../doc/assets
COQDOCFLAGS:= \
  --no-externals \
  --toc --toc-depth 2 --html \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
