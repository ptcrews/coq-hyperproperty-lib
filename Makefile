FLAGS := -Q . VFA  -arg "-w -omega-is-deprecated,-implicit-core-hint-db"

FILES := Hyperproperty.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(FLAGS) -o Makefile.coq $(FILES)

-include Makefile.coq

.PHONY: build clean
