targets = automata.vo pds.vo
srcs = equiv.v stack.v automata.v pds.v
vobjs = $(srcs:.v=.vo)

.PHONY: clean all default doc distclean
%.vo: %.v
	coqc $<

default: automata.vo pds.vo
all: $(targets)
automata.vo pds.vo: stack.vo
stack.vo: equiv.vo

doc: $(vobjs)
	coqdoc --gallina $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) *.html *.css
