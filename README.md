# Cyclist for QSL

*Cyclist* is a framework for building cyclic theorem provers based on a sequent calculus, an instantiation for Quantitative Separation Logic is located in the folder src/quantitative_seplog and recursive definition examples in examples/qsl.defs. The rest of the code is from the original *Cyclist* [Github repository](https://github.com/cyclist-org/cyclist) and additional information can be found on their website [www.cyclist-prover.org](http://www.cyclist-prover.org). The theory behind the QSL instantiation is in my thesis "Etailments in Quantitative Separation Logic with Recursive Definitions: Constructing Cyclic Proofs".

## Building

You can find building hints on [www.cyclist-prover.org](http://www.cyclist-prover.org). These are my additional notes on modules and versions with which the compilation worked for me:
```
gcc >= 11.4.0 (definitely works with 12.1.0)
ocaml 4.08.0
dune 3.10.0
hashset 1.0.0
ocaml-hashcons 1.0.1
re 1.11.0
mparser 1.3
```

And here are notes on how I built ocaml, dune, and spot (I did not have root access).
```
OCAML
./configure --prefix ~/ocaml -with-debug-runtime CC='gcc -fcommon'
make world
make install

DUNE
./configure --libdir ~/dune/lib --bindir ~/dune/bin --sbindir ~/dune/sbin --mandir ~/dune/man --docdir ~/dune/doc --etcdir ~/dune/etc --datadir ~/dune/datashare
make release
make install

SPOT
./configure --prefix ~/spot -disable-python-features
make
make install
```

Additionally, it could help setting some environment variables if you install the programs to a custom directory.
```
PATH: ocaml bin, dune bin, spot bin, cyclist_qsl/_build/install/default/bin
CPLUS_INCLUDE_PATH: spot include
LD_LIBRARY_PATH: spot lib, ocaml lib, dune lib
LIBRARY_PATH: spot lib
```

## Usage

The command for the QSL instantiation of Cyclist is qsl_prove. You need to provide a sequent to prove with -S "(sequent)". Use -h to show the list of possible arguments.
The allowed syntax for QSL entailments is
```
Entailment -> Form |- Form
Form -> Disjunct \/ Form | Disjunct
Disjunct -> Summand + Disjunct | Summand
Summand -> Atom * Summand | Atom
Atom -> emp | x | a=b | a!=b | a->b | P(c1,...,cn)
```
where x is a non-negative rational number and a, b and c_i are variables or nil.
If you want to play with the code and experiment with a specific proof and rule applications, you can use -test and look at prove.ml and change the lines starting from line 179.

The syntax for recursive definitions can be seen in qsl.defs.
The definitions in qsl.defs are not all proven to express what they should express or be precise / conform with other definitions, so use them with care or as example starting points. The length of the Empty versions of definitions is one more than the length of the non empty versions (e.g. ListEmptyLen evaluates to 2 for a list a->b and ListLen evaluates to 1 for the same list).

