.PHONY: all watch demo

all:
	dune build ./main.exe --display=quiet && dune exec ./main.exe --display=quiet

watch:
	dune build ./main.exe -w

demo:
	dune build demo/d.exe && dune exec demo/d.exe --display=quiet

arith:
	dune build demo/arith_demo.exe && dune exec demo/arith.exe --display=quiet

clean:
	@dune clean

freq:
	sudo cpupower frequency-set --governor performance

