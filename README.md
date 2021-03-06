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
git clone --depth 1 --branch v0.0.2 https://bitbucket.org/uog-bigraph/bigraph-tools uog-bigraph-tools-0.0.2
cd uog-bigraph-tools-0.0.2
dune build --profile=release
dune install --profile=release
cd ..
git clone https://github.com/zajer/trs/
opam install csv zarith parmap ounit2
dune build --profile=release
dune install --profile=release
```

### Installing library so it is listed as an OPAM package
If you want to install both libraries (`bigraph` and `tracking_bigraph`) so they are listed in opam via ``opam list`` you can do it with a minor tweak.

 - Once you clone bigraph-tools go to the project root directory;
 - Open ``dune-project`` file;
 - Add the following line before package definitions:
        
        (name bigrapher)
    At the time of writing this, the begining of the file will look similar to this:
    ```
    (lang dune 2.5)
    (source (uri https://bitbucket.org/uog-bigraph/bigraph-tools/))
    (license BSD-3-Clause)
    (authors "Michele Sevegnani" "Blair Archibald")
    (maintainers "michele.sevegnani@glasgow.ac.uk")
    (homepage "http://www.dcs.gla.ac.uk/~michele/bigrapher.html")
    (documentation "http://www.dcs.gla.ac.uk/~michele/doc/index.html")
    (generate_opam_files true)
    (name bigrapher)
    
    ```
 - Now instead of installing both libraries with ``dune install --profile=release`` you can do it with ``opam install .``


### Troubleshooting with installation
In case installing `bigraph-tools` results in errors, below are some additional steps that may help in solving them:
```
apt install minisat zlib1g-dev
opam install menhir jsonm cmdliner
```
If for some reason building `minisat` fails with ``library dune.configurator not found`` here is what fixed this for me: 
```
opam install .
```
Please note that the above command won't succeed. It merely allows to proceed with installation of `bigraph-tools` by installing/configuring its dependencies. In my case it was the lack of `dune.configurator`.

<sup>1</sup> It has been verified to work with version `0.0.2`. Versioning according to: https://bitbucket.org/uog-bigraph/bigraph-tools/downloads/?tab=tags

## Usage

See the file(s) in the `example` folder.

For more in depth description of the idea behind this tool and possible use case scenarios please refer to this paper: https://www.mdpi.com/1424-8220/21/2/622
