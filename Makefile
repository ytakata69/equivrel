targets = after.vo after_r.vo after_l.vo register_type.vo

.PHONY: clean all
%.vo: %.v
	coqc $<

all: $(targets)
$(targets): equiv.vo

clean:
	$(RM) *.vo *.glob .*.aux *~
