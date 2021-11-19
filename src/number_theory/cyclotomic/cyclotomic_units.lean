/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.polynomial.field_division
import number_theory.number_field
import number_theory.cyclotomic.basic
import ready_for_mathlib.roots_of_unity
import ready_for_mathlib.cyclotomic

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
  by_cases hyzero : y = 0,
  { simp only [hyzero, span_singleton_eq_bot, span_zero_singleton],
    exact ⟨λ h, by { exact ⟨1, by simp [h]⟩ }, λ ⟨h₁, h₂⟩, by simpa [smul_eq_zero_iff_eq] using h₂⟩ },
  by_cases hxzero : x = 0, { simp [eq_comm, hxzero], },
  have hx : x ∈ span R ({x} : set M) := mem_span_singleton_self _,
  have hy : y ∈ span R ({y} : set M) := mem_span_singleton_self _,
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← h at hy, obtain ⟨v, hv⟩ := submodule.mem_span_singleton.1 hy,
    rw [h] at hx, obtain ⟨w, hw⟩ := submodule.mem_span_singleton.1 hx,
    have hwv : w * v = 1,
    { rw [← one_smul R x, ← hv, ← smul_assoc] at hw,
      simpa using smul_left_injective R hxzero hw },
    have hvw : v * w = 1,
    { rw [← one_smul R y, ← hw, ← smul_assoc] at hv,
      simpa using smul_left_injective R hyzero hv },
    refine ⟨⟨v, w, hvw, hwv⟩, by simpa using hv⟩ },
  { obtain ⟨u, rfl⟩ := h,
    refine le_antisymm (span_le.2 _) (span_le.2 (by simp [submodule.mem_span_singleton_self])),
    rw [set.singleton_subset_iff, set_like.mem_coe, submodule.mem_span_singleton],
    exact ⟨↑u⁻¹, by simp [units.smul_def, ← smul_assoc]⟩ }
end

end movethis

namespace is_cyclotomic_extension

variables [is_cyclotomic_extension {n} A B]

include A n
/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta' n A B` is any root of
`cyclotomic n A` in L. -/
def zeta' : B :=
classical.some (ex_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

@[simp]
lemma zeta'_spec : aeval (zeta' n A B) (cyclotomic n A) = 0 :=
classical.some_spec (ex_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

lemma zeta'_spec' : is_root (cyclotomic n B) (zeta' n A B) :=
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
begin
  rw is_root_cyclotomic_iff,
  convert zeta'_spec' n A B,
  sorry,
  -- NOTE: (hn : (↑n : B) ≠ 0) is definitely necessary here. is this worth passing through TC?
  -- This sorry is `exact_mod_cast hn`, but I currently don't want to break build until we
  -- find the right solution to this. ~Eric
end

/-- The `power_basis` given by `zeta' n A B`. -/
--not true in general.. over a field and?
def zeta'.power_basis : power_basis A B :=
{ gen := zeta' n A B,
  dim := finite_dimensional.finrank A B,
  basis := sorry,
  basis_eq_pow := sorry }

lemma zeta'.power_basis_gen : (zeta'.power_basis n A B).gen = zeta' n A B := rfl

/-- `zeta'.embeddings_equiv_primitive_roots` is the equiv between `B →ₐ[A] C` and
  `primitive_roots n C` given by the choice of `zeta'`. -/
--this should be proved using `power_basis.lift_equiv` (check if a more general version is ok).
--false in general. True over ℚ and?
def zeta'.embeddings_equiv_primitive_roots (K C : Type*) [field K] [algebra A K]
  [is_cyclotomic_extension {n} A K] [comm_ring C] [algebra A C] [is_domain C] : (K →ₐ[A] C) ≃ primitive_roots n C :=
{ to_fun := λ σ, ⟨σ (zeta' n A K), (mem_primitive_roots n.pos).2 (is_primitive_root.of_injective
    (alg_hom.to_ring_hom σ).injective (zeta'_primitive_root n A K))⟩,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

--This proof will be `rfl` or not depending on the def of `zeta'.embeddings_equiv_primitive_roots`.
@[simp] lemma zeta'.embeddings_equiv_primitive_roots_apply {K C : Type*} [field K] [algebra A K]
  [is_cyclotomic_extension {n} A K] [comm_ring C] [algebra A C] [is_domain C] (σ : K →ₐ[A] C) :
  ↑(zeta'.embeddings_equiv_primitive_roots n A K C σ) = σ (zeta' n A K) := sorry

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

lemma zeta_coe : ((zeta n K) : (cyclotomic_field n K) ) = (zeta' n K (cyclotomic_field n K)) := rfl

lemma zeta_primitive_root :
  is_primitive_root (zeta n K : ring_of_integers (cyclotomic_field n K)) n :=
begin
  let f := algebra_map (ring_of_integers (cyclotomic_field n K)) (cyclotomic_field n K),
  let hf : function.injective f := sorry, --library_search finds the right thing but it times out?
  rw is_primitive_root.injective_iff hf,
  convert zeta'_primitive_root n _ _,
  apply_instance
end

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
