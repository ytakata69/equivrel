targets = after.vo after_r.vo after_l.vo register_type.vo grammar.vo

.PHONY: clean all default
%.vo: %.v
	coqc $<

default: equiv.vo register_type.vo
all: $(targets)
$(targets): equiv.vo
grammar.vo: equiv.vo after.vo after_r.vo after_l.vo register_type.vo

clean:
	$(RM) *.vo *.glob .*.aux *~
