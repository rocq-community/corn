<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# C-CoRN

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/corn/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/corn/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



CoRN includes the following parts:

- Algebraic Hierarchy

  An axiomatic formalization of the most common algebraic
  structures, including setoids, monoids, groups, rings,
  fields, ordered fields, rings of polynomials, real and
  complex numbers

- Model of the Real Numbers

  Construction of a concrete real number structure
  satisfying the previously defined axioms

- Fundamental Theorem of Algebra

  A proof that every non-constant polynomial on the complex
  plane has at least one root

- Real Calculus

  A collection of elementary results on real analysis,
  including continuity, differentiability, integration,
  Taylor's theorem and the Fundamental Theorem of Calculus

- Exact Real Computation

  Fast verified computation inside Coq. This includes: real numbers, functions,
  integrals, graphs of functions, differential equations.


## Meta

- Author(s):
  - Evgeny Makarov
  - Robbert Krebbers
  - Eelis van der Weegen
  - Bas Spitters
  - Jelle Herold
  - Russell O'Connor
  - Cezary Kaliszyk
  - Dan Synek
  - Luís Cruz-Filipe
  - Milad Niqui
  - Iris Loeb
  - Herman Geuvers
  - Randy Pollack
  - Freek Wiedijk
  - Jan Zwanenburg
  - Dimitri Hendriks
  - Henk Barendregt
  - Mariusz Giero
  - Rik van Ginneken
  - Dimitri Hendriks
  - Sébastien Hinderer
  - Bart Kirkels
  - Pierre Letouzey
  - Lionel Mamane
  - Nickolay Shmyrev
  - Vincent Semeria
- Coq-community maintainer(s):
  - Bas Spitters ([**@spitters**](https://github.com/spitters))
  - Vincent Semeria ([**@vincentse**](https://github.com/vincentse))
  - Xia Li-yao ([**@Lysxia**](https://github.com/Lysxia))
- License: [GNU General Public License v2](LICENSE)
- Compatible Coq versions: Coq 8.19 or greater
- Additional dependencies:
  - [Math-Classes](https://github.com/coq-community/math-classes) 8.8.1 or
greater, which is a library of abstract interfaces for mathematical
structures that is heavily based on Coq's type classes.

  - [Bignums](https://github/com/coq/bignums)
- Coq namespace: `CoRN`
- Related publication(s):
  - [See this page for the list of publications](http://corn.cs.ru.nl/pub.html) 

## Building and installation instructions

The easiest way to install the latest released version of C-CoRN
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-corn
```

To instead build and install manually, you have to start with
the `bignums` dependency:

``` shell
git clone https://github.com/coq/bignums
cd bignums
make   # or make -j <number-of-cores-on-your-machine>
make install
```

The last `make install` is necessary, it copies `bignums` to
a common folder, which is usually `coq/user-contrib`. Afterwards
the similar commands for `math-classes` will find `bignums` there.
Finally build `corn` itself:

``` shell
git clone https://github.com/coq-community/corn
cd corn
./configure.sh
make   # or make -j <number-of-cores-on-your-machine>
make install
```

### Building C-CoRN with SCons

C-CoRN supports building with [SCons](http://www.scons.org/). SCons is a modern
Python-based Make-replacement.

To build C-CoRN with SCons run `scons` to build the whole library, or
`scons some/module.vo` to just build `some/module.vo` (and its dependencies).

In addition to common Make options like `-j N` and `-k`, SCons
supports some useful options of its own, such as `--debug=time`, which
displays the time spent executing individual build commands.

`scons -c` replaces Make clean

For more information, see the [SCons documentation](http://www.scons.org/).

### Building documentation

To build CoqDoc documentation, say `scons coqdoc`.



