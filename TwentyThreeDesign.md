# Regular-prime 23 proof design

## Honest target

`FltRegular.NumberTheory.RegularPrimes` defines

```lean
IsRegularPrime 23 =
  23.Coprime (Fintype.card
    (ClassGroup (NumberField.RingOfIntegers (CyclotomicField 23 ℚ))))
```

so a PID instance is unnecessary and, for the 23rd cyclotomic field, would be
false.  The smallest convenient certificate is

```lean
∀ c : ClassGroup (NumberField.RingOfIntegers (CyclotomicField 23 ℚ)), c ^ 3 = 1
```

or equivalently

```lean
Monoid.exponent
  (ClassGroup (NumberField.RingOfIntegers (CyclotomicField 23 ℚ))) ∣ 3.
```

`BealRegular/TwentyThreeDesign.lean` proves, using Cauchy's theorem, that
either certificate implies `IsRegularPrime 23`.  An exact-cardinality theorem
with cardinality `3` is stronger than needed and is exposed only as an
alternative endpoint.  None of these endpoints asserts the external class
group computation.

## Reusable local and mathlib APIs

- `ClassGroup.mk0_surjective` represents every class by a nonzero integral
  ideal.
- `NumberField.exists_ideal_in_class_of_norm_le` chooses such a representative
  below the Minkowski bound.
- `Ideal.prod_normalizedFactors_eq_self` and
  `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors` reduce a bounded
  ideal to bounded prime ideals.
- `ClassGroup.mk0_eq_one_iff` turns a principal ideal certificate into a class
  relation; together with `map_pow`, principality of `P ^ 3` proves
  `(ClassGroup.mk0 P) ^ 3 = 1`.
- `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime`
  already contains almost exactly the prime-factor reduction needed, but its
  conclusion hard-codes principality of `P`, not principality of `P ^ 3`.
- The Galois reduction in
  `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`
  shows how to check one prime above each rational prime.  Its use of
  `inertiaDeg_eq_of_isGaloisGroup`, `exists_smul_eq_of_isGaloisGroup`,
  `Ideal.map_pow`, and `Submodule.IsPrincipal.map_ringHom` also preserves the
  property that `P ^ 3` is principal.
- `IsCyclotomicExtension.Rat.pid1` through `pid6` provide the
  Kummer-Dedekind/factor-polynomial and logarithmic-bound plumbing that can be
  generalized from `P.IsPrincipal` to `(P ^ 3).IsPrincipal`.

## Implemented generic lemmas

`BealRegular/ClassGroupExponentMinkowski.lean` now proves and kernel-audits two
reusable theorems, with no 23-specific computation:

```lean
theorem classGroup_pow_eq_one_of_isPrincipal_pow_of_norm_le_of_isPrime
    (e : ℕ)
    (h : ∀ (P : (Ideal (NumberField.RingOfIntegers K))⁰),
      (P : Ideal (NumberField.RingOfIntegers K)).IsPrime →
      absNorm (P : Ideal (NumberField.RingOfIntegers K)) ≤ M K →
      Submodule.IsPrincipal ((P : Ideal (NumberField.RingOfIntegers K)) ^ e)) :
    ∀ c : ClassGroup (NumberField.RingOfIntegers K), c ^ e = 1
```

and the Galois convenience form

```lean
theorem classGroup_pow_eq_one_of_one_prime_above
    [IsGalois ℚ K] (e : ℕ)
    (h : ∀ p ∈ Finset.Icc 1 ⌊M K⌋ₙ, p.Prime →
      ∃ P ∈ primesOver (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers K),
        ⌊M K⌋ₙ < p ^ P.inertiaDeg ℤ ∨
          Submodule.IsPrincipal (P ^ e)) :
    ∀ c : ClassGroup (NumberField.RingOfIntegers K), c ^ e = 1
```

The first proof uses the bounded representative and normalized-factor
argument from `ClassNumber.lean`, replacing membership in the submonoid of
principal ideals by membership after raising to `e`.  The second proof copies
the existing Galois conjugacy argument and inserts `Ideal.map_pow` before
applying `Submodule.IsPrincipal.map_ringHom`.  Their dedicated audit reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
`TwentyThreeDesign.lean` connects both generic statements directly to
`IsRegularPrime 23` through cube-principality.

## Polynomial certificate for a cubed prime ideal

For a Kummer-Dedekind ideal

```text
P = (q, F(θ))
```

a kernel-checkable certificate that `P ^ 3 = (G(θ))` can consist solely of
integer-polynomial identities modulo `Φ23`:

```text
q³       = G Q0 + Φ23 R0
q² F     = G Q1 + Φ23 R1
q F²      = G Q2 + Φ23 R2
F³        = G Q3 + Φ23 R3
G        = C0 q³ + C1 q²F + C2 qF² + C3 F³ + Φ23 R4.
```

The first four identities prove `P ^ 3 ≤ (G(θ))`; the last proves the
reverse inclusion.  This is the exponent-three analogue of the polynomial
Bezout witnesses consumed by `pid4`/`pid6`, and it trusts no Sage result until
Lean checks every identity.  `BealRegular/CubicIdealCertificate.lean` now
implements this verifier over an arbitrary commutative ring, its `aeval`
polynomial bridge, the constant-polynomial Kummer--Dedekind specialization,
and the direct `Submodule.IsPrincipal` endpoint.  Its dedicated audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Compact real-subfield and relative-class-number route

There is a second possible route which avoids the `28,283` full-field prime
certificates. Let `K = ℚ(ζ₂₃)` and let `K⁺` be its maximal real subfield. A
normalized defining polynomial for `K⁺`, with generator
`a = -(ζ₂₃ + ζ₂₃⁻¹)`, is

```text
f(Y) = Y^11 - Y^10 - 10Y^9 + 9Y^8 + 36Y^7 - 28Y^6
       - 56Y^5 + 35Y^4 + 35Y^3 - 15Y^2 - 6Y + 1.
```

The dependency-free script
`scripts/TwentyThreeRelativeClassNumber.mjs` checks the following exact
integer arithmetic:

- the Laurent-polynomial identity
  `X^11 * f(-(X + X⁻¹)) = -Φ₂₃(X)`;
- the polynomial discriminant
  `disc(f) = 23^10 = 41426511213649`, using a Sylvester resultant and a
  fraction-free Bareiss determinant;
- the exact totally-real Minkowski interval
  `900 < 11! * 23^5 / 11^11 < 901`;
- using the usual real-cyclotomic residue degree, namely the order of `q` in
  `(ℤ/23ℤ)ˣ/{±1}`, the only unramified rational primes with
  `q^f ≤ 900` are

  ```text
  47, 137, 139, 229, 277, 367, 461, 599, 643, 691, 827, 829;
  ```

- `5` has order `22` modulo `23`, and for

  ```text
  A(T) = Σ (5^j mod 23) T^j,  0 ≤ j ≤ 21,
  ```

  whose ascending coefficients are

  ```text
  1, 5, 2, 10, 4, 20, 8, 17, 16, 11, 9,
  22, 18, 21, 13, 19, 3, 15, 6, 7, 12, 14,
  ```

  the exact odd-character resultant is

  ```text
  Res(T^11 + 1, A(T))
    = -127262242448329728
    = -3 * 46^10.
  ```

Run the audit with:

```bash
node --check scripts/TwentyThreeRelativeClassNumber.mjs
CODEX_WORK_TAG=twenty-three-relative node --title=work:twenty-three-relative \
  scripts/TwentyThreeRelativeClassNumber.mjs
```

These computations do **not** prove either class number. The missing
cyclotomic relative class-number formula is the theorem which would identify

```text
|Res(T^11 + 1, A(T))| / 46^10
```

with the relative class number `h⁻(K) = h(K) / h(K⁺)`. Once that theorem is
available, the checked resultant reduces `h⁻(K) = 3` to integer arithmetic.
An unconditional full proof along this route would still need:

1. a Lean identification of the displayed degree-11 model with `K⁺`, including
   its ring of integers and discriminant;
2. principal-ideal certificates above the twelve displayed unramified primes
   and the ramified prime `23`, to prove `h(K⁺) = 1`;
3. the relative class-number formula itself. Mathlib has useful ingredients
   (`NumberField.DedekindZeta`, the CM-field regulator ratio, cyclotomic
   Dirichlet characters, functional equations, Gauss sums, and resultants),
   but it does not currently assemble them into this formula.

Thus this is a compact, concrete research program, not a completed Lean
bridge. The shortest conceptual endpoint remains Kummer's Bernoulli
criterion, whose finite `p = 23` side is already checked in
`TwentyThreeBernoulli.lean`; that criterion is also still missing.

The
[LMFDB page for `K`](https://www.lmfdb.org/NumberField/22.0.39471584120695485887249589623.1)
reports class group `[3]`, class number `3`, and relative class number `3`.
The
[LMFDB page for the degree-11 real field](https://www.lmfdb.org/NumberField/11.11.41426511213649.1)
reports class number `1`. Those are explicitly **external database facts**:
the script does not import them, and no Lean declaration in this repository
uses them.

## Scale audit and recommended route

For `K = ℚ(ζ₂₃)`, the standard cyclotomic discriminant formula gives the
Minkowski value approximately `9,324,406.48`, hence floor `9,324,406`.
A direct sieve of rational primes satisfying

```text
q ^ orderOf(q mod 23) ≤ 9,324,406
```

finds `28,283` primes other than `23`: `28,262` of order one, `19` of order
two, and `2` of order eleven.  Therefore a mechanical `pid6`-style extension
with one cube-principality witness per rational prime is a valid fallback but
is not a sensible first implementation.

The scale calculation and sieve are dependency-free and reproducible with:

```bash
node --check scripts/TwentyThreeDesignCount.mjs
CODEX_WORK_TAG=twenty-three-design node --title=work:twenty-three-design \
  scripts/TwentyThreeDesignCount.mjs
```

The script uses `BigInt` fixed-point intervals to establish the displayed
Minkowski floor and exact integer arithmetic for the prime-power cutoff.  It is
research evidence only and is not trusted by any Lean theorem.

The [LMFDB field page](https://www.lmfdb.org/NumberField/22.0.39471584120695485887249589623.1)
and its direct [`nf_fields` JSON query](https://www.lmfdb.org/api/nf_fields/?label=22.0.39471584120695485887249589623.1&_format=json)
report `class_group: [3]` and `class_number: 3` for the degree-22 field with
conductor `23` and defining polynomial `x^22 - x^21 + ... - x + 1`, which is
isomorphic to `ℚ(ζ₂₃)`.  This is explicitly **external database evidence**, not a
Lean theorem and not an input to any declaration in
`BealRegular/TwentyThreeDesign.lean`.

The preferred research route is:

1. The generic `CubicIdealCertificate` verifier and the first concrete case
   are complete. `TwentyThreePrimeTwoCube.lean` proves that the degree-11
   factor selected modulo `2` defines a prime above `2` and kernel-checks its
   principal cube. The deterministic SymPy witness finder and independent
   BigInt validator preserve the discovery and validation pipeline. This one
   class relation does not prove that the class group is generated by it.
2. In parallel, investigate a compact certified class-group presentation:
   a finite generating set of ideal classes, relations showing every generator
   cubes to one, and a proven surjection onto the class group.  Only the
   surjection and exponent-three relations are needed; independence and exact
   cardinality are not.
3. Develop the real-subfield/relative-class-number route above as an
   independent exact-class-number program: thirteen real-subfield ideal
   certificates plus the currently missing relative class-number formula.
   The dependency-free script fixes its finite target data but proves neither
   missing bridge.
4. If no compact unconditional presentation is available, formalize Kummer's
   Bernoulli criterion as a separate theorem.  The finite side is now complete:
   `TwentyThreeBernoulli.lean` kernel-computes `B_2` through `B_20`, their
   reduced numerators, and the fact that none is divisible by `23`.  Mathlib
   and this checkout still lack the theorem connecting that condition to
   divisibility of the cyclotomic class number.  That Kummer bridge, not the
   finite Bernoulli calculation for `23`, is the substantial missing
   mathematics.
5. Use the 28,283-witness Minkowski route only as a last-resort generated proof,
   split into independently checked chunks from the start.

An exact proof that the class group has cardinality `3` would additionally
need a lower-bound/nonprincipality argument.  It provides no benefit for FLT
at exponent `23`; proving exponent dividing `3` is the deliberately weaker and
better-scoped goal.
