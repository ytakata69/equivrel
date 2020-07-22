targets = after.vo after_r.vo after_l.vo register_type.vo

.PHONY: clean all default
%.vo: %.v
	coqc $<

default: equiv.vo
all: $(targets)
$(targets): equiv.vo

clean:
	$(RM) *.vo *.glob .*.aux *~
