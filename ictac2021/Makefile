targets = 

.PHONY: clean all default
%.vo: %.v
	coqc $<

default: equiv.vo
all: $(targets)
#$(targets): equiv.vo

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~
