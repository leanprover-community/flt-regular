/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.polynomial.field_division
import number_theory.number_field

import number_theory.cyclotomic.basic

noncomputable theory

open_locale big_operators non_zero_divisors
open number_field polynomial finset module units fractional_ideal submodule

universes u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

section movethis

-- TODO redefine span_singleton as a monoid hom so we get this for free?
@[simp]
lemma span_singleton_pow {R : Type*} {P : Type*} [comm_ring R] {S : submonoid R} [comm_ring P]
  [algebra R P] [loc : is_localization S P] (x : P) : ∀ (n : ℕ),
  span_singleton S (x ^ n) = span_singleton S x ^ n
| 0 := by simp
| (n + 1) := by simp [pow_succ, ← span_singleton_pow n]

-- pretty sure there is an easier proof of this
lemma submodule.span_singleton_eq_span_singleton {R : Type*} {M : Type*} [ring R] [add_comm_group M]
  [module R M] [no_zero_smul_divisors R M] (x y : M) :
  span R ({x} : set M) = span R ({y} : set M) ↔ ∃ u : units R, u • x = y :=
begin
  by_cases hy : y = 0,
  { subst hy,
    simp,
    split; intro h,
    { subst h,
      use 1,
      simp, },
    { cases h,
      simpa [smul_eq_zero_iff_eq] using h_h, -- TODO this lemma should be simp
      }, },
  by_cases hx : x = 0,
  { subst hx,
    simp [eq_comm], },  -- TODO LOL why is this case so much easier
  rw [le_antisymm_iff, and_comm, submodule.le_span_singleton_iff, submodule.le_span_singleton_iff],
  split; intro h,
  { rcases h with ⟨h_left, h_right⟩,
    obtain ⟨u, hu⟩ := h_left y (mem_span_singleton_self y),
    obtain ⟨v, hv⟩ := h_right x (mem_span_singleton_self x),
    use [u, v],
    { rw [← hv, ← mul_smul, ← sub_eq_zero] at hu,
      rw ← one_smul R y at hu {occs := occurrences.pos [2]},
      rw [← sub_smul, smul_eq_zero, sub_eq_zero] at hu,
      tauto, },
    { rw [← hu, ← mul_smul, ← sub_eq_zero] at hv,
      rw ← one_smul R x at hv {occs := occurrences.pos [2]},
      rw [← sub_smul, smul_eq_zero, sub_eq_zero] at hv,
      tauto, },
    exact hu, },
  { rcases h with ⟨h, rfl⟩,
    simp [submodule.mem_span_singleton],
    split; intro a,
    { use [a * h],
      simp [mul_smul];
      refl, },
    { use [a * (h⁻¹ : units R)],
      rw mul_smul,
      congr,
      rw [smul_def h x, ← mul_smul],
      simp only [one_smul, inv_mul], }, },
end

end movethis

namespace is_cyclotomic_extension

variables [is_cyclotomic_extension {n} A B]

include A n
/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta' n A B` is any root of
`cyclotomic n A` in L. -/
def zeta' : B :=
classical.some (((iff _ _ _).1 (show is_cyclotomic_extension {n} A B, from infer_instance)).1
  n (set.mem_singleton n))

@[simp]
lemma zeta'_spec :
  aeval (zeta' n A B) (cyclotomic n A) = 0 := sorry

lemma zeta'_spec' :
  is_root (map (algebra_map A B) (cyclotomic n A)) (zeta' n A B) :=
begin
  simp only [is_root.def, map_cyclotomic],
  convert zeta'_spec n A B,
  rw [aeval_def, eval₂_eq_eval_map],
  simp [-zeta'_spec]
end

--This shouldn't be needed.
variable [is_domain B]

@[simp]
lemma zeta'_pow_prime : (zeta' n A B) ^ (n : ℕ) = 1 :=
begin
  suffices : is_root (X ^ (n : ℕ) - 1) (zeta' n A B),
  { simpa [sub_eq_zero], },
  rw [← prod_cyclotomic_eq_X_pow_sub_one n.pos, is_root.def, eval_prod, finset.prod_eq_zero_iff],
  use n,
  simp only [n.pos.ne.symm, true_and, nat.mem_divisors, ne.def, not_false_iff, dvd_refl],
  have := zeta'_spec n A B,
  rw [aeval_def, eval₂_eq_eval_map] at this,
  convert this,
  rw map_cyclotomic,
end

lemma zeta'_primitive_root : is_primitive_root (zeta' n A B) n :=
{ pow_eq_one := zeta'_pow_prime n A B,
  dvd_of_pow_eq_one := sorry }

-- TODO use the fact that a primitive root is a unit.
-- TODO prove in general that is_primitive root is integral,
-- this exists as is_primitive_root.is_integral so use

end is_cyclotomic_extension

namespace cyclotomic_ring

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

open is_cyclotomic_extension

lemma zeta'_integral :
  zeta' n K (cyclotomic_field n K) ∈ ring_of_integers (cyclotomic_field n K) :=
begin
  show is_integral ℤ (zeta' n _ _),
  use [cyclotomic n ℤ, cyclotomic.monic n ℤ],
  rw [← zeta'_spec n K (cyclotomic_field n K)],
  simp [aeval_def, eval₂_eq_eval_map],
end

--zeta' should be in `(cyclotomic_ring n A K)` by definition.
lemma zeta'_mem_base : ∃ (x : (cyclotomic_ring n A K)), algebra_map
  (cyclotomic_ring n A K) (cyclotomic_field n K) x = zeta' n K (cyclotomic_field n K) := sorry

--zeta should be in `units (cyclotomic_ring n A K)` by definition.
/-- `zeta n K L` is a root of `cyclotomic n K` in
`units (ring_of_integers (cyclotomic_field n K))`. -/
def zeta : units (ring_of_integers (cyclotomic_field n K)) :=
units.mk_of_mul_eq_one
  (⟨zeta' n _ _, zeta'_integral n _⟩)
  (⟨zeta' n K _, zeta'_integral n _⟩ ^ ((n : ℕ) - 1))
  begin
    ext,
    simp [← pow_succ, nat.sub_add_cancel n.pos],
  end

lemma zeta_primitive_root :
  is_primitive_root (zeta n K : ring_of_integers (cyclotomic_field n K)) n :=
{ pow_eq_one := sorry,
  dvd_of_pow_eq_one := sorry }
-- is_primitive_root.of

lemma zeta_pow_eq_one : (zeta n K) ^ (n : ℕ) = 1 :=
begin
  ext,
  rw zeta,
  simp,
end

/-- `aux` is a hacky way to define the inverse mod `n`, probably its best to replace it with an
actual inverse in `zmod n`. -/
def aux (r n : ℕ) : ℕ := ((r.gcd_a n) % n).nat_abs

lemma aux_spec {r n : ℕ} (h : r.coprime n) : r * aux r n ≡ 1 [MOD n] := sorry

section cyclotomic_unit

variable {n}

local notation `RR` := ring_of_integers (cyclotomic_field n K)
local notation `L` := cyclotomic_field n K

--cyclotomic_unit should be in `units (cyclotomic_ring n A K)` by definition.
--Also think if generalize, maybe a group?
--Once final def is done, add docstring and remove noling.
@[nolint doc_blame unused_arguments]
def cyclotomic_unit {r s : ℕ} (hr : r.coprime n) (hs : s.gcd n = 1) :
  units (ring_of_integers (cyclotomic_field n K)) :=
units.mk_of_mul_eq_one
  (geom_sum ((zeta n K) ^ s) (r * aux r n))
  -- (∑ t in range r, zeta hn ^ (s * t))
  --(( zeta n ^r - 1) * ((zeta n)^s - 1)⁻¹)
  (geom_sum ((zeta n  K) ^ r) (s * aux r n))
  -- (∑ t in range s,  zeta hn ^ (t * r))
  begin
    sorry;
    { simp,
    rw sum_mul,
    simp [mul_sum],
    norm_cast,
    simp only [← pow_add],
    simp,
    sorry, },
  end

namespace cyclotomic_unit

lemma mul_denom {r s : ℕ} (hr : r.coprime n) (hs : s.coprime n) :
  (cyclotomic_unit K hr hs : RR) * ((zeta n K) ^ s - 1) = (zeta n K) ^ r - 1 := sorry

lemma exists_unit_mul_primitive_root_one_sub_zeta  (z : RR)
  (hz : is_primitive_root z n) :
  ∃ u : units RR, ↑u * (1 - z : RR) = 1 - (zeta n K) :=
begin
  -- have := zeta_primitive_root n,
  rw is_primitive_root.is_primitive_root_iff (zeta_primitive_root n K) n.pos at hz,
  obtain ⟨i, hip, hin, hi⟩ := hz,
  rw ← hi,
  refine ⟨(cyclotomic_unit K (nat.gcd_one_left _) hin), _⟩,
  rw ← neg_sub,
  rw mul_neg_eq_neg_mul_symm,
  simp [mul_denom K (nat.gcd_one_left _) hin],
end

variable (n)

instance : is_localization ((ring_of_integers (cyclotomic_field n K)))⁰ (cyclotomic_field n K) :=
sorry

lemma prime_ideal_eq_pow_cyclotomic [hn : fact ((n : ℕ).prime)] :
  (span_singleton _ n : fractional_ideal RR⁰ L) =
  (span_singleton _ (1 - (zeta n K)) ^ ((n : ℕ) - 1) : fractional_ideal RR⁰ L) :=
  --(mk0 (p : cyclotomic_field p) (by norm_num [hn.ne_zero]))
begin
  rw ← span_singleton_pow,
  apply coe_to_submodule_injective,
  simp only [coe_span_singleton, coe_coe],
  -- rw ideal.span_singleton_eq_span_singleton,
  simp only [submodule.span_singleton_eq_span_singleton],
  rw ← eval_one_cyclotomic_prime,
  --rw calc
  --  eval 1 (cyclotomic n (cyclotomic_field n)) = _ : by simp_rw
  --    cyclotomic_eq_prod_X_sub_primitive_roots (zeta'_primitive_root n _)
  --                      ... = _ : by simp only [polynomial.eval_sub, polynomial.eval_C,
  --                                  polynomial.eval_prod, polynomial.eval_X],

  -- apply span_singleton_eq_span_singleton_,
  sorry,
end

end cyclotomic_unit

end cyclotomic_unit

end cyclotomic_ring
