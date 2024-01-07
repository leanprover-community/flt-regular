import Mathlib.FieldTheory.KummerExtension
import FltRegular.NumberTheory.AuxLemmas
import Mathlib.RingTheory.Norm
/-!
# Kummer Theory

## Main result
- `isCyclic_tfae`:
Suppose `L/K` is a finite extension of dimension `n`, and `K` contains all `n`-th roots of unity.
Then `L/K` is cyclic iff
`L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
`L = K[α]` for some `αⁿ ∈ K`.

- `autEquivRootsOfUnity`:
Given an instance `IsSplittingField K L (X ^ n - C a)`
(perhaps via `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`),
then the galois group is isomorphic to `rootsOfUnity n K`, by sending
`σ ↦ σ α / α` for `α ^ n = a`, and the inverse is given by `μ ↦ (α ↦ μ • α)`.

- `autEquivZmod`:
Furthermore, given an explicit choice `ζ` of a primitive `n`-th root of unity, the galois group is
then isomorphic to `Multiplicative (ZMod n)` whose inverse is given by
`i ↦ (α ↦ ζⁱ • α)`.

## Other results
Criteria for `X ^ n - C a` to be irreducible is given:
`X_pow_sub_C_irreducible_iff_of_prime`: `X ^ n - C a` is irreducible iff `a` is not a `p`-power.

TODO: criteria for general `n`.

-/
variable {K : Type*} [Field K]

open Polynomial IntermediateField AdjoinRoot

section Irreducible

-- TODO: use this to prove the case where the degree is arbitrary
theorem X_pow_sub_C_irreducible_of_prime {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a) := by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a)
  · rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hp.pos, Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor this (X_pow_sub_C_ne_zero hp.pos a)
  -- It suffices to show that `deg g = p`.
  suffices natDegree g = p from (associated_of_dvd_of_natDegree_eq hg'
    (this.trans natDegree_X_pow_sub_C.symm) (X_pow_sub_C_ne_zero hp.pos a)).irreducible hg
  by_contra h
  have : Fact (Irreducible g) := ⟨hg⟩
  let Kx := AdjoinRoot g
  -- Let `r` be a root of `g`, then `N_K(r) ^ p = N_K(r ^ p) = N_K(a) = a ^ (deg g)`.
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ p = a ^ g.natDegree
  · have htop : Subalgebra.toSubmodule (⊤ : IntermediateField K Kx).toSubalgebra = ⊤ := rfl
    have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hg' (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at this
    rw [← map_pow, this, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
      ← finrank_top, ← htop, ← IntermediateField.adjoin_adjoinRoot_root_eq_top g,
      Subalgebra.finrank_toSubmodule, finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin.finrank,
      AdjoinRoot.minpoly_root hg.ne_zero, natDegree_mul_C]
    · simpa using hg.ne_zero
    · exact AdjoinRoot.isIntegral_root hg.ne_zero
  -- Since `a ^ (deg g)` is a `p`-power, and `p` is coprime to `deg g`, we conclude that `a` is
  -- also a `p`-power, contradicting the hypothesis
  have : p.Coprime (natDegree g) := hp.coprime_iff_not_dvd.mpr (fun e ↦ h (((natDegree_le_of_dvd hg'
    (X_pow_sub_C_ne_zero hp.pos a)).trans_eq natDegree_X_pow_sub_C).antisymm (Nat.le_of_dvd
      (natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg) e)))
  exact ha _ (mem_range_pow_of_coprime_of_pow_mem_range_pow this.symm a ⟨_, key⟩).choose_spec

theorem X_pow_sub_C_irreducible_iff_of_prime {p : ℕ} (hp : p.Prime) (a : K) :
    Irreducible (X ^ p - C a) ↔ ∀ b : K, b ^ p ≠ a := by
  refine ⟨?_, X_pow_sub_C_irreducible_of_prime hp⟩
  contrapose!
  rintro ⟨α, rfl⟩ H
  have := degree_eq_one_of_irreducible_of_root H (x := α) (by simp)
  rw [degree_X_pow_sub_C hp.pos, Nat.cast_eq_one] at this
  exact hp.ne_one this

end Irreducible
