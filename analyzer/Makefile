
run: checker
	./checker data

checker.o: checker.c densemat.h
	gcc -c -O2 -DCHECK_AGAINST_REF checker.c

densemat.o: densemat.c densemat.h alloc.h
	gcc -c -O2 densemat.c

alloc.o: alloc.c alloc.h
	gcc -c -O2 alloc.c

checker: checker.o densemat.o alloc.o
	gcc checker.o densemat.o alloc.o -o checker

LAPROOF= $(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/LAProof/C

densemat.c: $(LAPROOF)/src/densemat.c
	cp $< $@

alloc.c: $(LAPROOF)/src/alloc.c
	cp $< $@

densemat.h: $(LAPROOF)/include/densemat.h alloc.h
	cp $< $@

alloc.h: $(LAPROOF)/include/alloc.h
	cp $< $@

clean:
	rm checker checker.o densemat.o
