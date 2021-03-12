# Tracking_bigraph
An addon to the OCaml library "Bigraph".
It allows tracking of nodes between state transitions.

## Credits
This is just an addon to the `bigraph` library available here: https://bitbucket.org/uog-bigraph/bigraph-tools.
It uses some code for rewriting bigraphs from the original library. Hence, the original author is included in the LICENSE file.

## Installation
You gonna need `bigraph`<sup>1</sup> and `onauty` libraries installed in order to compile and install this one.

In a nutshell, the process of installing this library on a debian-like system will look like this:

(assumed `opam` and `dune` are installed)
```
apt install libnauty2-dev
git clone https://github.com/zajer/onauty/
cd onauty
dune build
opam install .
cd ..
git clone https://github.com/zajer/conf-nauty/
cd conf-nauty
opam install .
cd ..
cd uog-bigraph-tools-0.0.2
dune build --profile=release
dune install --profile=release
cd ..
git clone https://github.com/zajer/trs/
opam install csv zarith parmap ounit2
dune build --profile=release
dune install --profile=release
```

In case installing `bigraph-tools` results in errors, below are some additional steps that may help in solving them:
```
apt install minisat zlib1g
opam install menhir jsonm cmdliner
```

<sup>1</sup> It has been verified to work with version `0.0.2` according to: https://bitbucket.org/uog-bigraph/bigraph-tools/downloads/?tab=tags

## Usage

See the file(s) in the `example` folder.

For more in depth description of the idea behind this tool and possible use case scenarios please refer to this paper: https://www.mdpi.com/1424-8220/21/2/622
