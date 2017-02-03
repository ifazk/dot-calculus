COQC=coqc

FILES=dot_definitions.v dot_top_bot.v



OBJECTS=$(FILES:.v=.vo)

INCLUDESDIR=../../../ln/tlc/
LIBLN=$(INCLUDESDIR)/LibLN.vo

all: $(OBJECTS)

$(LIBLN):
	cd $(INCLUDESDIR) && make

%.vo:%.v
	$(COQC) -I $(INCLUDESDIR) $^

.PHONY:clean

clean:
	rm $(OBJECTS) $(FILES:.v=.glob)
