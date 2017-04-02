FILES=dot_top_bot.v
OBJECTS=$(FILES:.v=.vo)

PROOFS=$(FILES)
PROOFOBJECTS=$(PROOFS:.v=.vo)

TLCDIR=../../../ln/tlc/
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME)
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

########################
# Library Dependencies #
########################

$(LIBLN):
	cd $(TLCDIR) && make

###################
# Forced Rebuilds #
###################
$(PROOFMAKEFILE): .FORCE
	@$(COQMAKEFILE) $(COQINCLUDE) -install none $(PROOFS) > $@

_CoqProject: .FORCE
	@echo $(COQINCLUDE) > $@

.FORCE:

