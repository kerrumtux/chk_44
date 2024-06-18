SHELL=bash
CFLAGS=-D X64 --coverage -g -Wno-pointer-to-int-cast -Wno-int-to-pointer-cast -Wno-int-conversion
LDFLAGS="-lgcov"

inter:  main.c eval.c symbols.c objects.c parser.c lexer.c arith.c str.c array.c pair.c predicates.c alloc.c
	gcc $(CFLAGS) $(LDFLAGS) -o $@ $^

build: inter
	cp test/inter_run ./cl-inter
