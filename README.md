# Fermat's Last Theorem for regular primes
The goal of this project is to prove Fermat's Last Theorem for [regular primes](https://en.wikipedia.org/wiki/Regular_prime)
in [Lean](https://leanprover-community.github.io/).

## Beal companion extension

The `BealRegular` library adds assumption-free, kernel-checked FLT coverage for
every equal exponent `3 <= n <= 22`.  Composite exponents are reduced to the
formal FLT theorems at `3`, `4`, `5`, `7`, `11`, `13`, `17`, or `19`.  The
same reduction excludes a mixed-power equation whenever one of those integers
from `3` through `22` divides all three exponents.

The regular-prime results at `17` and `19` are proved here by exact cyclotomic
PID certificates, not by assuming their class numbers.  Sage was used only to
discover the integer-polynomial witnesses.  Lean checks all `103` certificates
for `17` and all `558` certificates for `19`; independent Node validators
check the generated data and dispatch tables, and the renderers are byte-
idempotent.

Exponent `23` is deliberately separated from the unconditional range.  The
project kernel-checks the finite Bernoulli numerator condition and proves that
an exponent-three certificate for the cyclotomic class group would imply
regularity and FLT23.  `BealRegular/CubicIdealCertificate.lean` also verifies
the exact five-polynomial certificate showing that a Kummer--Dedekind ideal
has principal cube.  `BealRegular/TwentyThreePrimeTwoCube.lean` applies that
checker to a concrete irreducible degree-11 factor modulo `2`, identifies the
resulting prime ideal above `2`, and proves its cube principal.
`BealRegular/TwentyThreePrimeThreeCube.lean` checks the analogous certificate
for a prime above `3`.  Galois conjugacy makes one selected prime sufficient
for each rational prime, so these two relations finish the two degree-11
rational primes in the full-field Minkowski sieve.  They do not prove that
every class has exponent three: `28,262` degree-one and `19` degree-two
rational primes, as well as the ramified prime, remain on that brute-force
route.  The project does not assume Kummer's Bernoulli criterion or claim that
the non-PID cyclotomic field is a PID.  See `TwentyThreeBernoulli.md` and
`TwentyThreeDesign.md` for the explicit proof routes and remaining gap.

Useful verification commands are:

```sh
lake build BealRegular
lake env lean BealRegularAudit.lean
node scripts/validate_17_certificates.mjs
node scripts/validate_19_certificates.mjs
node scripts/validate_23_prime2_cube_certificate.mjs
node scripts/validate_23_prime3_cube_certificate.mjs
```

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
