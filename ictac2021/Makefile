targets = automata.vo

.PHONY: clean all default
%.vo: %.v
	coqc $<

default: equiv.vo automata.vo
all: $(targets)
$(targets): equiv.vo

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~
