# Fermat's Last Theorem for regular primes
The goal of this project is to prove Fermat's Last Theorem for [regular primes](https://en.wikipedia.org/wiki/Regular_prime)
in [Lean](https://leanprover-community.github.io/).

The following readme has been shamelessly copied from the [Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid/).

## How to browse this repository

### Blueprint

Here are a draft [blueprint](https://leanprover-community.github.io/flt-regular/blueprint) and  [dependency graph](https://leanprover-community.github.io/flt-regular/blueprint/dep_graph_document.html).

### Getting the project

The recommended way of browsing this repository is by using a Lean development environment.
Crucially, this will allow you to inspect Lean's "Goal state" during proofs,
and easily jump to definitions or otherwise follow paths through the code. Please use the
[installation instructions](https://leanprover-community.github.io/get_started.html#regular-install)
to install Lean and a supporting toolchain.
After that, download and open a copy of the repository
by executing the following command in a terminal:
```
git clone https://github.com/leanprover-community/flt-regular.git
cd flt-regular
lake exe cache get
lake build
code .
```
For detailed instructions on how to work with Lean projects,
see [this](https://leanprover-community.github.io/install/project.html).

You can also use gitpod and do everything directly in your browser, without installing anything.
Just click on [![Gitpod](https://img.shields.io/badge/Gitpod-ready--to--code-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/flt-regular), but beware that everything will be slower than on your computer.

### Reading the project

With the project opened in VScode,
you are all set to start exploring the code.
There are two pieces of functionality that help a lot when browsing through Lean code:

* "Go to definition": if you right-click on a name of a definition or lemma
  (such as `is_regular_number`, or `flt_regular_case_one`), then you can choose "Go to definition" from the menu,
  and you will be taken to the relevant location in the source files.
  This also works by `Ctrl`-clicking on the name.
* "Goal view": in the event that you would like to read a *proof*,
  you can step through the proof line-by-line,
  and see the internals of Lean's "brain" in the Goal window.
  If the Goal window is not open,
  you can open it by clicking on one of the icons in the top right hand corner.

### Organization of the project

* All the Lean code (the juicy stuff) is contained in the directory `FltRegular/`.
* The file `FltRegular/FltRegular.lean` contains the statement of Fermat's Last Theorem for
  regular primes.
* The ingredients that go into the theorem statement are defined in several other files.
  The most important pieces are:
  - `NumberTheory/RegularPrimes.lean` we give the definition of what a regular number is.
  - `NumberTheory/*` are the files we are actively working on.
  - `ReadyForMathlib/*` are the files that are (almost) ready to be PRed to mathlib.

Note that we are trying to move all our results to mathlib as fast as possible, so the
folder `ReadyForMathlib` changes rapidly. You should also check `Mathlib.NumberTheory.Cyclotomic.*`.

## Brief note on type theory

Lean is based on type theory,
which means that some things work slightly differently from set theory.
We highlight two syntactical differences.

* Firstly, the element-of relation (`∈`) plays no fundamental role.
  Instead, there is a typing judgment (`:`).

  This means that we write `x : X` to say that "`x` is a term of type `X`"
  instead of "`x` is an element of the set `X`".
  Conveniently, we can write `f : X → Y` to mean "`f` has type `X → Y`",
  in other words "`f` is a function from `X` to `Y`".

* Secondly, type theorists use lambda-notation.
  This means that we can define the square function on the integers via
  `fun x ↦ x^2`, which translates to `x ↦ x^2` in set-theoretic notation.
  For more information about `λ` (called `fun` in Lean 4), see the Wikipedia page on
  [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus).

For a more extensive discussion of type theory,
see the dedicated
[page](https://leanprover-community.github.io/lean-perfectoid-spaces/type_theory.html)
on the perfectoid project website.

[![Gitpod ready-to-code](https://img.shields.io/badge/Gitpod-ready--to--code-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/flt-regular)
