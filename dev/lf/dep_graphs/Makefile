FILE=Dpdgraph.v

DPDFILES=tight_wo_defs.dpd tight_wo_defs_slem.dpd
DOTFILES=$(DPDFILES:.dpd=.dot)
PDFFILES=$(DPDFILES:.dpd=.pdf)
FILES=$(DPDFILES) $(DOTFILES) $(PDFFILES)

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
pdf:: $(PDFFILES)
dot:: $(DOTFILES)
dpd:: $(DPDFILES)

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

#########
# Clean #
#########

.PHONY: clean
clean::
	@echo "Cleaning"
	@rm -rf $(FILES)

##################
# Original Proof #
##################
ORIGFILE=Dpdgraph_orig.v

ORIGDPDFILES=orig_wo_defs.dpd orig_wo_defs_slem.dpd
ORIGDOTFILES=$(ORIGDPDFILES:.dpd=.dot)
ORIGPDFFILES=$(ORIGDPDFILES:.dpd=.pdf)

ORIGFILES= $(ORIGDPDFILES) $(ORIGDOTFILES) $(ORIGPDFFILES)

ORIGTOPDIR=../orig-proof/
ORIGSAFETY=$(ORIGTOPDIR)Dot_proofs_safety.vo

$(ORIGDPDFILES): TOPDIR=$(ORIGTOPDIR)
$(ORIGDPDFILES): SAFETY=$(ORIGSAFETY)
$(ORIGDPDFILES): $(ORIGFILE) $(ORIGSAFETY)
	coqtop $(COQINCLUDE) < $(ORIGFILE)

pdf:: $(ORIGPDFFILES)
dot:: $(ORIGDOTFILES)
dpd:: $(ORIGDPDFILES)

clean::
	@rm -rf $(ORIGFILES)
