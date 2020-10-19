.PHONY: all watch demo

all:
	dune build ./main.exe --display=quiet && dune exec ./main.exe --display=quiet

watch:
	dune build ./main.exe -w

demo:
	dune build demo/d.exe && dune exec demo/d.exe  --display=quiet

clean:
	@dune clean

