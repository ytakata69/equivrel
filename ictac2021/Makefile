targets = automata.vo
srcs = equiv.v automata.v
vobjs = $(srcs:.v=.vo)

.PHONY: clean all default doc distclean
%.vo: %.v
	coqc $<

default: equiv.vo automata.vo
all: $(targets)
$(targets): equiv.vo

doc: $(vobjs)
	coqdoc --gallina $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) *.html *.css
