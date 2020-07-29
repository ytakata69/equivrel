targets = after.vo after_r.vo after_l.vo register_type.vo grammar.vo

.PHONY: clean all default
%.vo: %.v
	coqc $<

default: equiv.vo register_type.vo
all: $(targets)
$(targets): equiv.vo
after_l.vo: register_type.vo after.vo
after_r.vo: register_type.vo after.vo
grammar.vo: register_type.vo after.vo after_r.vo after_l.vo

clean:
	$(RM) *.vo *.glob .*.aux *~
