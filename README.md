# Tracking_bigraph
An addon to the OCaml library "Bigraph".
It allows tracking of nodes between state transitions.

## Credits
This is just an addon to the `bigraph` library, available here: https://bitbucket.org/uog-bigraph/bigraph-tools.
It uses some code for rewriting bigraphs from the original library. Hence, the original author is included in the LICENSE file.

## Installation
As of 2022 the easiest way to install this library on Debian-like operating system is to do the following on a system with OCaml 4.13 and opam installed:
- Clone source code of bigraph-tools v0.0.2
```
git clone --dept 1 --branch v0.0.2 https://bitbucket.org/uog-bigraph/bigraph-tools uog-bigraph-tools-0.0.2
```
- Install `dune`,`dune-configurator`,`jsonm.1.0.1`,`cmdliner.1.0.4`,`menhir.20200123`,`ounit2`, `csv`, `parmap` and `zarith`  via opam:
```
opam install dune dune-configurator jsonm.1.0.1 cmdliner.1.0.4 menhir.20200123 ounit2 csv parmap zarith
```
- Install `minisat` and `zlib1g-dev` via package manager:
```
apt-get install minisat zlib1g-dev
```
- Install bigraph-tools from previously downloaded source:
```
cd uog-bigraph-tools-0.0.2
dune build
dune install
cd ..
```
- Download sources of `conf-nauty`, `onauty` and `trs` packages:
```
git clone https://github.com/zajer/conf-nauty
git clone https://github.com/zajer/onauty
git clone https://github.com/zajer/trs
```
- Install `libnauty2-dev` via package manager:
```
apt-get install libnauty2-dev
```
- Pin `conf-nauty` package to the downloaded source:
```
cd conf-nauty
opam install .
cd ..
```
- Install `onauty`:
```
cd onauty
dune build
dune install
cd ..
```
- Finally install `trs` library from source:
```
cd trs
dune build
dune install
```

## Usage

See the file(s) in the `example` folder.

For more in depth description of the idea behind this tool and possible use case scenarios please refer to this paper: https://www.mdpi.com/1424-8220/21/2/622
