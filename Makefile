FILES := Hyperproperties.v CrashSystem.v GuaranteedService.v ObservationalDeterminism.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq $(FILES)

-include Makefile.coq

.PHONY: build clean
