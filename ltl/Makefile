.PHONY: clean all
%.vo: %.v
	coqc $<

all: mu.vo monotonic.vo automata.v

monotonic.vo: mu.vo
automata.vo: mu.vo monotonic.vo

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~
