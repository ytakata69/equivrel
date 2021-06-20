targets = automata.vo pds.vo
srcs = equiv.v automata.v pds.v
vobjs = $(srcs:.v=.vo)

.PHONY: clean all default doc distclean
%.vo: %.v
	coqc $<

default: equiv.vo automata.vo pds.vo
all: $(targets)
$(targets): equiv.vo

doc: $(vobjs)
	coqdoc --gallina $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) *.html *.css
