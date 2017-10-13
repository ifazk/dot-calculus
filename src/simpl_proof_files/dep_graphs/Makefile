FILE=Dpdgraph.v

DPDFILES=graph.dpd
DOTFILES=$(DPDFILES:.dpd=.dot)
PDFFILES=$(DPDFILES:.dpd=.pdf)
FILES=$(DPDFILES) $(DOTFILES) $(PDFFILES)

TOPDIR=../../simple-proof/proof/
TOPNAME=""
SAFETY=$(TOPDIR)Safety.vo

TLCDIR=../../simple-proof/lib/tlc
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME) -R $(TOPDIR) $(TOPNAME)

##############
# Main Rules #
##############

.PHONY: dpd dot pdf

pdf:: $(PDFFILES)
dot:: $(DOTFILES)
dpd:: $(DPDFILES)

$(DPDFILES): $(FILE) $(SAFETY)
	coqtop $(COQINCLUDE) < $(FILE)

$(SAFETY): $(TOPDIR)/*.v
	cd $(TOPDIR) && make

%.dot: %.dpd
	dpd2dot -without-defs $<

%.pdf: %.dot
	dot -Tpdf $< > $@

########################
# Library Dependencies #
########################

$(LIBLN):
	cd $(TLCDIR) && make

###################
# Forced Rebuilds #
###################

.FORCE:

#########
# Clean #
#########

.PHONY: clean
clean::
	@echo "Cleaning"
	@rm -rf $(FILES)
