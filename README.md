# bitvector-mk


Installation

```
opam switch create ./ --repositories=default,index --packages=ocaml-variants.4.14.2+index,ocaml-option-flambda --no-install
```

And install dependecies....


#### Less tested but should work

```
opam switch create ./ --no-install --repositories=default,index --packages=ocaml-variants.4.14.2+index,ocaml-option-flambda,indexing-tools,mtime,logger-p5,bisect_ppx,ppx_inline_test,ppx_expect,res,z3,benchmark
```

Current issue

```
✗ dune b GT -j1 --verbose
...
Running[1]: (cd _build/default && /home/kakadu/asp/bitvector-mk/_opam/bin/ocaml-index aggregate --root /home/kakadu/asp/bitvector-mk -o GT/plugins/.syntax_all.objs/cctx.ocaml-index)
File "GT/plugins/.syntax_all.objs/_unknown_", line 1, characters 0-0:
Command [1] exited with code 124:
$ (cd _build/default && /home/kakadu/asp/bitvector-mk/_opam/bin/ocaml-index aggregate --root /home/kakadu/asp/bitvector-mk -o GT/plugins/.syntax_all.objs/cctx.ocaml-index)
ocaml-uideps: a required argument is missing
Usage: ocaml-uideps aggregate [OPTION]… ARG…
Try 'ocaml-uideps aggregate --help' or 'ocaml-uideps --help' for more information.
```