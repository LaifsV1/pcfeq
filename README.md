# pcfeq
Bisimulation Checking tool for PCFv programs

## Directory Structure

Directories present under the main `pcfeq` directory:
- `experiments`: experimental data as recorded for the submitted paper, also attached here
- `programs`: our testsuite, which is divided into subdirectories for equivalences `equiv` and inequivalences `inequiv`
- `src`: source files of pcfeq

## Installation

Instructions below were tested for Linux and macOS. `opam` is not yet officially supported for Windows.

Dependencies:
- OCaml 4.08+ with `ocamlbuild`
- Opam
- Menhir
- Z3 with OCaml bindings

### Installing OCaml's Package Manager `opam`

All dependencies are obtainable through OCaml's official package manager [`opam`](http://opam.ocaml.org/doc/Install.html). Installation of `opam` is system specific so you may need to refer to their website linked above. Instructions for some popular systems are listed below:
#### Ubuntu
```
add-apt-repository ppa:avsm/ppa
apt update
apt install opam
```
#### Fedora, CentOS and RHEL
```
dnf install opam
```
#### macOS
```
# Homebrew
brew install gpatch
brew install opam

# MacPort
port install opam
```

### Initialising `opam`

`opam` needs to be set up after installation, and this may be system dependent. First one needs to initialise it:
```
opam init
```
After initialisation, one has to create the switch to a specific compiler. Any version 4.08 and over works. The command below uses `4.08.1`, but one can use the latest version listed.
```
opam switch create 4.08.1
```
If this does not work, it could be because `opam` is missing a dependency. Depending on how minimal the installation of the system is, one may have to install many dependencies. You may need to check the error messages to know what is missing. In our experience, these are the dependencies typically missing e.g. for Ubuntu:
```
apt install build-essential
apt install gcc
apt install bubblewrap
```
The above correspond to `make`, `gcc` and `bwrap`, which are often missing in fresh installations.

Finally, initialising `opam` updates your `~/.profile` file, so you may have to source it on e.g. Ubuntu:
```
source ~/.profile
```

### Installing `pcfeq`'s dependencies

With `opam` set up, installing `pcfeq`'s dependencies becomes very easy.
```
opam install ocamlbuild
opam install menhir
opam install z3
```
Note that Z3 takes a long time to install.

With all dependencies installed and `~/.profile` sourced, call the make file:
```
make
```
This produces a `pcfeq.native` binary.

## Usage

`pcfeq` inputs a file containing two program expressions, written in `pcfeq`’s input language which is based on ML. `pcfeq` attempts to (dis-)prove that the expressions are contextually equivalent. That is, replacing one for another in any possible program context does not change the observable behaviour of the program. See the paper for more details on contextual equivalence.

### Tool Options

The primary options necessary for usage are:

- `-i <input file path>`: selects a file to check; otherwise, `pcfeq` expects input via `stdin`
- `-b <integer bound>`: number of function applications `pcfeq` is allowed to perform before returning an "incoclusive" result to the user

For list of options available under each parameter, use `--help`.

### Testing Script

A script is provided to run our experiments as described in the paper.

Note that this script requires `timeout` from GNU Coreutils. All files checked are set to time out after 150s. Also note that the compiled binary `pcfeq.native` needs to be in the main directory (with the script) for the script to work.

The script can be called as follows:

```
bash run-tests.sh
```

The script can output 1 of 4 messages for every file:
- `equivalent`: the terms have been proven contextually equivalent
- `inequivalent`: the terms have been proven contextually inequivalent
- `inconclusive`: `pcfeq` reached the bound and could not prove equivalence or inequivalence
- `error`: `pcfeq` stopped unexpectedly, which can be for the following reasons:
  - **message is present in the log files**: `pcfeq` crashed and the message details the reasons. None of the provided examples in our experiments produce this case.
