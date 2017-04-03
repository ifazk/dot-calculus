FILE=Dpdgraph.v

DPDFILE=file_depend.dpd
DOTFILE=$(DPDFILE:.dpd=.dot)
PDFFILE=$(DPDFILE:.dpd=.pdf)

TOPDIR=../tight-proof/
TOPNAME=""
SAFETY=$(TOPDIR)Safety.vo

TLCDIR=../../../ln/tlc/
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME) -R $(TOPDIR) $(TOPNAME)

##############
# Main Rules #
##############

.PHONY: dpd dot pdf
pdf: $(PDFFILE)

dot: $(DOTFILE)

dpd: $(DPDFILE)

$(DPDFILE): $(FILE) $(SAFETY)
	coqtop $(COQINCLUDE) < $(FILE)

$(DOTFILE): $(DPDFILE)
	dpd2dot -without-defs $(DPDFILE)

$(PDFFILE): $(DOTFILE)
	dot -Tpdf $(DOTFILE) > $(PDFFILE)

########################
# Library Dependencies #
########################

$(SAFETY):
	cd $(TOPDIR) && make

$(LIBLN):
	cd $(TLCDIR) && make

###################
# Forced Rebuilds #
###################

.FORCE:
