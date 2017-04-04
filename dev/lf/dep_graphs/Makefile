FILE=Dpdgraph.v

DPDFILES=file_depend_wo_defs.dpd file_depend_wo_defs_slem.dpd
DOTFILES=$(DPDFILES:.dpd=.dot)
PDFFILES=$(DPDFILES:.dpd=.pdf)

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
pdf: $(PDFFILES)

dot: $(DOTFILES)

dpd: $(DPDFILES)

$(DPDFILES): $(FILE) $(SAFETY)
	coqtop $(COQINCLUDE) < $(FILE)

%.dot: %.dpd
	dpd2dot -without-defs $<

%.pdf: %.dot
	dot -Tpdf $< > $@

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
