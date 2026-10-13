# Mathlib upstreaming audit

Audit date: 2026-09-02

This review covers all 25 Lean modules under `FltRegular/` (3,968 lines), including the
unused-declaration report in `docs/unseen_defs.txt`. It was performed against mathlib commit
`1ed178f0ecb4003157c8dd82fd7b293603b4e083` (2026-08-31).

The ordering below favours, in this order:

1. a clear home and API fit in mathlib;
2. absence of an existing equivalent;
3. downstream value to this project or to number theory generally;
4. small review and maintenance cost.

“Ready” means that the mathematical statement and Lean proof are complete and that only normal PR
work remains: moving the declaration, minimizing imports, choosing a mathlib-style name, adding a
docstring, and possibly making proof-only helpers private. It does not mean that the current file
should be copied verbatim.

## Verification summary

- The repository contains no `sorry`, `admit`, or project axioms.
- Every shortlisted declaration checked with `#print axioms` uses only the standard axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build` succeeds.
- Direct source compilation with
  `lake env lean FltRegular/NumberTheory/Hilbert92.lean` also succeeds.

## Ready upstream PRs, in priority order

### 1. Conductor-two cyclotomic equivalence and PID theorem

Source:

- [`cyclotomicFieldTwoEquiv`](FltRegular/NumberTheory/RegularPrimes.lean#L42)
- [`IsPrincipalIdealRing_of_IsCyclotomicExtension_two`](FltRegular/NumberTheory/RegularPrimes.lean#L51)

Verdict: **ready after light packaging; best first PR**.

The first declaration proves that a field cyclotomic at `{2}` is algebra-equivalent to the base
field. The second transports the PID structure of `ℤ` to the ring of integers. No equivalent was
found in the pinned mathlib. The PID result fills the conspicuous gap immediately before
`IsCyclotomicExtension.Rat.three_pid` and `.five_pid`.

Recommended upstream shape:

- put the equivalence in `Mathlib/NumberTheory/Cyclotomic/Basic.lean`, under
  `IsCyclotomicExtension`, with a name such as `algEquiv_of_two`;
- expose a theorem, not a global instance, named `IsCyclotomicExtension.Rat.two_pid` in
  `Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean`;
- retain the concrete `CyclotomicField 2 ℚ` instances locally only if the project still needs
  them.

The nearest existing result, `IsCyclotomicExtension.algEquiv`, compares two cyclotomic
extensions; it does not identify conductor two with the base field.

### 2. The seventh cyclotomic field has class number one

Source: [`Rat.seven_pid`](FltRegular/SmallNumbers/Seven/Seven.lean#L69)

Verdict: **mathematically ready; repackage the proof using current mathlib**.

Mathlib's cyclotomic PID file currently contains `three_pid` and `five_pid`, and its module
documentation explicitly says that the method continues through conductor 19. This makes
`IsCyclotomicExtension.Rat.seven_pid` an unusually clear contribution with a pre-existing API
and destination:
`Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean`.

Before opening the PR:

- move the theorem into the existing `IsCyclotomicExtension.Rat` namespace;
- make the Minkowski-bound and explicit-polynomial calculations private or give them descriptive
  names;
- replace the global `Nat.fact_prime_seven` instance with a local instance;
- prove the result directly from
  `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`
  and `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`;
- do not upstream the one-use `pid1`--`pid6` chain or the specialized `orderOf_lt_of` merely to
  support this proof.

### 3. Norm as a product of powers of a cyclic generator

Source: [`norm_eq_prod_pow_gen`](FltRegular/NumberTheory/Hilbert92.lean#L183)

Verdict: **ready after naming and documentation**.

Mathlib has `Algebra.norm_eq_prod_automorphisms`, but no explicit formula that enumerates a cyclic
Galois group by the powers of a chosen generator. The proof is short, generic, and compiles as part
of the complete Hilbert 92 source file.

Recommended upstream shape:

- name it along the lines of `Algebra.norm_eq_prod_powers`;
- consider expressing the generator hypothesis as `Subgroup.zpowers σ = ⊤` if that composes more
  naturally with the existing cyclic-group API;
- place it beside `Algebra.norm_eq_prod_automorphisms` in
  `Mathlib/RingTheory/Norm/Transitivity.lean` (or in the nearest non-cyclic import that avoids a
  cycle).

### 4. Unit-rank formula for extensions unramified at infinity

Source:
[`NumberField.Units.rank_of_isUnramified`](FltRegular/NumberTheory/Hilbert92.lean#L586)

Verdict: **ready after light cleanup**.

This gives

```text
rank O_L^x = [L : K] * rank O_K^x + [L : K] - 1
```

when `L/K` is unramified at every infinite place. It combines Dirichlet's unit-rank definition
with `IsUnramifiedAtInfinitePlaces.card_infinitePlace`; no theorem with this conclusion was found.
There is good API precedent in `IsCMField.units_rank_eq_units_rank`.

Recommended upstream work:

- rename it to an equality-shaped name such as
  `NumberField.Units.rank_eq_of_isUnramifiedAtInfinitePlaces`;
- add a docstring;
- choose a location at the Dirichlet-theorem/infinite-ramification boundary while checking for an
  import cycle.

The proof is only a few lines and compiles as part of the complete Hilbert 92 source file.

### 5. Reduced-minimal-polynomial criterion for unramifiedness

Source:

- [`isUnramifiedAt_of_Separable_minpoly'`](FltRegular/NumberTheory/Unramified.lean#L112)
- [`isUnramifiedAt_of_Separable_minpoly`](FltRegular/NumberTheory/Unramified.lean#L147)

Verdict: **ready after API cleanup; highest-leverage structural PR**.

The theorem says that if an integral primitive element has separable minimal polynomial after
reduction modulo the prime below `P`, then the integral closure is unramified at `P`. No equivalent
was found. The existing results `aeval_derivative_mem_differentIdeal` and
`not_dvd_differentIdeal_iff` are essential ingredients, not a replacement for this criterion.

Before upstreaming:

- rename `Separable` to lowercase `separable` in the declaration name;
- give the integral-closure-element version a descriptive name, or make it private if only the
  field-element version is public API;
- use `IsIntegralClosure.algebraMap_injective` directly instead of the local injectivity wrapper;
- add docstrings and split or golf the 34-line core proof;
- target `Mathlib/RingTheory/DedekindDomain/Different.lean` or the appropriate
  ramification/unramified module.

This should precede an attempt to upstream `KummersLemma.isUnramified`, which depends on it.

### 6. Cyclotomic Kummer congruences

Source:

- [`exists_dvd_pow_sub_Int_pow`](FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L32)
- [`quotient_zero_sub_one_comp_aut`](FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L45)
- [`zeta_sub_one_dvd_trace_sub_smul`](FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L67)
- [`zeta_sub_one_pow_dvd_norm_sub_pow`](FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L86)

Verdict: **ready as one coherent PR**.

These results respectively provide:

1. an integer whose `p`th power agrees with a cyclotomic integer's `p`th power modulo `p`;
2. invariance of reduction modulo `ζ - 1` under cyclotomic automorphisms;
3. the trace congruence modulo `ζ - 1`;
4. the norm congruence modulo `(ζ - 1)^p`.

All four are complete, use only mathlib imports, and have no exact equivalent in the pinned tree.
The quotient-map theorem may remain a private helper if reviewers do not want it as public API.

Recommended upstream work:

- add docstrings and put the public results under `IsPrimitiveRoot` or
  `IsCyclotomicExtension.Rat`;
- replace the `Int` fragment in names with mathlib's normal `intCast` terminology;
- use a new focused file such as
  `Mathlib/NumberTheory/NumberField/Cyclotomic/Congruences.lean` if the basic cyclotomic files
  would otherwise become too crowded;
- do not include `exists_zeta_sub_one_dvd_sub_Int`: it is already a direct specialization of
  `PowerBasis.exists_gen_dvd_sub`.

### 7. Divisibility of coefficients in a cyclotomic linear combination

Source:
[`dvd_coeff_cycl_integer`](FltRegular/NumberTheory/Cyclotomic/CyclRat.lean#L145)

Verdict: **ready after proof decomposition**.

If an integer divides a linear combination of all powers of a primitive prime-order root of unity,
and one integer coefficient is zero, then it divides every coefficient. The proof uses the
integral cyclotomic power basis and `Basis.dvd_coord_smul`; no corresponding theorem was found.
Although it lives in a project-oriented file, this declaration itself is mathlib-only.

Recommended upstream work:

- move it into a cyclotomic namespace and give it a conclusion-oriented name;
- add a docstring and minimize imports;
- extract the coordinate calculation into one or two reusable helpers so that the public proof is
  under mathlib's usual size threshold;
- place it in cyclotomic `Basic.lean` or in the congruence file proposed above.

### 8. A prime-normalized generator of a principal fractional-ideal quotient

Source:
[`exists_not_dvd_spanSingleton_eq`](FltRegular/CaseII/AuxLemmas.lean#L14)

Verdict: **genuinely new and standalone; ready after naming and decomposition**.

For a Dedekind domain, if `I / J` is principal and neither `I` nor `J` is divisible by the prime
principal ideal `(x)`, this theorem produces a generator `a / b` for which neither `a` nor `b` is
divisible by `x`. Existing fractional-ideal principality and localization lemmas produce a
numerator and denominator, but do not enforce the simultaneous nondivisibility condition.

Recommended upstream work:

- move it under `FractionalIdeal` with a name describing the normalized numerator and denominator;
- add a docstring;
- split the roughly 75-line valuation-cancellation argument into private helpers;
- target the fractional-ideal operations or Dedekind ideal lemmas file.

This declaration was already identified as intended for mathlib in the project's history, and it
still has no replacement in the current dependency.

## Valuable results that are not ready yet

These should not be opened as their current declarations, but they are plausible later PRs.

| Result | Why it is valuable | Blocking work |
| --- | --- | --- |
| [`norm_add_one_smul_of_isUnit`](FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L111) | An odd-prime congruence forces the integer norm of a unit `1 + p • x` to be `1`, not `-1`. | Generalize from number fields to the weakest finite-free commutative `ℤ`-algebra assumptions and state the hypothesis as essentially `2 < p`. |
| [`comap_map_eq_of_unramified`](FltRegular/NumberTheory/Unramified.lean#L41) | A Galois-invariant ideal in an unramified extension is extended from its contraction. No equivalent exists. | Generalize explicit fields and `galRestrict` to a finite action with `[IsGaloisGroup G R S]`, put it under `Ideal`, and split the 67-line factorization proof. |
| [`unit_inv_conj_is_root_of_unity`](FltRegular/NumberTheory/Cyclotomic/UnitLemmas.lean#L97) | Strengthens the CM-field torsion API by showing the unit/conjugate quotient is a square of a power of the chosen cyclotomic root. | Land the quotient-invariance congruence first; privatize preceding helpers; fix the `runity` typo; redesign the theorem name and namespace. |
| [`exists_pow_smul_eq_and_not_dvd`](FltRegular/NumberTheory/Hilbert92.lean#L357) | Extracts a maximal common `p`-power from a nonzero finite integer family. Existing multiplicity lemmas handle only one element. | Design an `Int`/`Pi`/`Finsupp` API and strengthen the surprising current hypothesis `p ≠ 1`, which permits `p = 0`, to the intended condition. |
| [`KummersLemma.isUnramified`](FltRegular/NumberTheory/KummersLemma/Field.lean#L311) | The Kummer extension cut out by `X^p - u` is unramified under the expected congruence. | First land priority 5; make the auxiliary-polynomial declarations private or package them as a small API. |
| [`exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one`](FltRegular/NumberTheory/KummersLemma/KummersLemma.lean#L31) and [`eq_pow_prime_of_unit_of_congruent`](FltRegular/NumberTheory/KummersLemma/KummersLemma.lean#L57) | The main regular-prime Kummer lemma is absent from mathlib. | It depends on the unramified Kummer extension and the current project-specific Hilbert 94 development. |
| [`IsRegularNumber`](FltRegular/NumberTheory/RegularPrimes.lean#L28) / [`IsRegularPrime`](FltRegular/NumberTheory/RegularPrimes.lean#L32) | Mathlib has no public regular-prime predicate. | Decide the API first: the present `IsRegularPrime` is only an alias and does not assert primality, so all callers also carry `[Fact p.Prime]`. |

The full Hilbert 92 and Hilbert 94 theorems should still wait. The current Hilbert 94 statement is
restricted to odd prime degree rather than the usual cyclic degree-`n` theorem, and both files
expose substantial proof scaffolding as public API.

## Use existing mathlib instead of upstreaming wrappers

The following declarations should be removed, inlined, or retained as project-local convenience
lemmas rather than proposed to mathlib.

| Local declaration or group | Existing mathlib route |
| --- | --- |
| `algebraMap_injective_of_isIntegralClosure` | Use `IsIntegralClosure.algebraMap_injective` together with the existing scalar-tower instances. |
| `Ideal.isPrincipal_pow_finrank_of_isPrincipal_map` | Compose `Ideal.relNorm_algebraMap`, the singleton-generator representation of the mapped principal ideal, and `Ideal.relNorm_singleton`. This is only a short wrapper. |
| `exists_zeta_sub_one_dvd_sub_Int` | Use `hζ.subOneIntegralPowerBasis.exists_gen_dvd_sub`. |
| `eq_one_mod_one_sub` | Use the quotient ideal API, in particular `Ideal.Quotient.mk_eq_one_iff_sub_mem`. |
| `complexConj_zeta` | Specialize `NumberField.IsCMField.complexConj_torsion`. |
| `roots_of_unity_in_cyclo` | Use `IsPrimitiveRoot.exists_pow_or_neg_mul_pow_of_isOfFinOrder`. |
| `diff_of_roots` and `diff_of_roots2` | Use `IsPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime`. |
| `uff` | Use `Nat.coprime_primes`. |
| The local cyclotomic `minpoly`, `exponent`, and `ne_dvd_exponent` lemmas | Compose `Polynomial.cyclotomic_eq_minpoly`, `RingOfIntegers.minpoly_coe`, `RingOfIntegers.exponent_eq_one_iff`, and `adjoin_singleton_eq_top`. |
| `orderOf_lt_of` | Use or modestly extend the general `orderOf_eq_iff`, `pow_ne_one_of_lt_orderOf`, and `orderOf_le_of_pow_eq_one` API; the current `ZMod` wrapper has one caller. |
| `PIDGalois` and `pid1`--`pid6` | For the current seventh-cyclotomic application, use the newer Galois PID criterion in `NumberField.ClassNumber` and cyclotomic `inertiaDeg_eq_of_not_dvd` directly. Keep `PIDGalois` only if an independent use justifies a generic Kummer--Dedekind bridge. |

`FltRegular/NumberTheory/CyclotomicRing.lean` should not be upstreamed as an alternative model.
Mathlib already has `CyclotomicRing`, its integral-closure theorem, the cyclotomic integral power
basis, the prime ideal generated by `ζ - 1`, and the relevant integer-divisibility API. Migrating
the project away from its `AdjoinRoot`-based `CyclotomicIntegers` would remove representation glue
and simplify `SystemOfUnits.lean` and `Hilbert92.lean`.

Likewise, the `poly*`, `map_poly*`, `polyRoot*`, `roots_poly`, `splits_poly`,
`minpoly_polyRoot*`, `separable_poly*`, and `mem_adjoin_polyRoot` declarations in
`KummersLemma/Field.lean` are scaffolding for the eventual public Kummer theorem, not separate API.
The preceding `zeta_sub_one_pow_dvd_poly` is a short composition of
`Polynomial.dvd_C_mul_X_sub_one_pow_add_one` and `associated_zeta_sub_one_pow_prime`. The FLT case
statements, descent steps, and `MayAssume` normalization lemmas should also remain project-local;
where they overlap library material, mathlib already exposes the general FLT normalization and
coprimality API in `Mathlib.NumberTheory.FLT.Basic`.

## Repository cleanup found during the audit

- Make proof-only declarations private, especially the auxiliary-polynomial chain in
  `KummersLemma/Field.lean` and the two `unit_inv_conj_not_neg_zeta_runity*` helpers.
- Fix the `runity` typo in those helper names.
- Localize the anonymous global `Algebra.IsAlgebraic K L` instance in `Hilbert94.lean` and the
  global primality fact for `7`.
- Redesign `RelativeUnits` before proposing it: the current `relativeUnitsWithGenerator` is a
  type-synonym workaround with unused parameters, and the `unitToU` identities should arise from
  a bundled homomorphism.
- The README still points readers to a deleted `ReadyForMathlib/` directory; replace that guidance
  with this file or remove it.
- `docs/unseen_defs.txt` contains 21 entries, most of which are generated `.congr_simp`
  declarations. The meaningful unused entries (`FLT_small`, `isRegularPrime_two`, and
  `isRegularPrime_three`) are either project-level results or depend on the unresolved regular-prime
  API, so unusedness alone does not make them upstream candidates.

## Suggested submission sequence

1. Conductor-two equivalence and `two_pid`.
2. `seven_pid`, rewritten against the current PID and inertia-degree API.
3. The cyclic norm formula.
4. The unit-rank formula.
5. The reduced-minimal-polynomial unramifiedness criterion.
6. The cyclotomic congruence package.
7. Cyclotomic coefficient divisibility.
8. Fractional-ideal prime-normalized generators.

After those land, revisit the generalized invariant-ideal theorem, the cyclotomic unit/conjugate
theorem, and the Kummer unramified-extension package in that dependency order.
