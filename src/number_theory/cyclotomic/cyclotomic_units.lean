/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.polynomial.field_division
import number_theory.number_field
import ready_for_mathlib.cyclotomic.basic
import ring_theory.polynomial.cyclotomic.eval
import ready_for_mathlib.cyclotomic
import ring_theory.adjoin.power_basis

noncomputable theory

open_locale big_operators non_zero_divisors
open number_field polynomial finset module units fractional_ideal submodule

universe variables u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

section movethis

-- TODO redefine span_singleton as a monoid hom so we get this for free?
@[simp]
lemma fractional_ideal.span_singleton_pow {R : Type*} {P : Type*} [comm_ring R] {S : submonoid R} [comm_ring P]
  [algebra R P] [loc : is_localization S P] (x : P) : ∀ (n : ℕ),
  span_singleton S (x ^ n) = span_singleton S x ^ n
| 0 := by simp
| (n + 1) := by simp [pow_succ, ← fractional_ideal.span_singleton_pow n]

-- TODO this really shouldn't be necessary either?
@[simp]
lemma fractional_ideal.span_singleton_prod {R : Type*} {P ι : Type*} [comm_ring R] {S : submonoid R} [comm_ring P]
  [algebra R P] [loc : is_localization S P] (T : finset ι) (I : ι → P) :
  span_singleton S (∏ t in T, I t) = ∏ t in T, span_singleton S (I t) :=
begin
  classical,
  induction T using finset.induction with i T hiT ih,
  { simp, },
  simp [hiT, span_singleton_mul_span_singleton, ih.symm],
end

@[simp]
lemma ideal.span_singleton_prod {R ι : Type*} [comm_ring R] (T : finset ι) (I : ι → R) :
  ideal.span ({∏ t in T, I t} : set R) = ∏ t in T, ideal.span {I t} :=
begin
  classical,
  induction T using finset.induction with i T hiT ih,
  { simp, },
  simp [hiT, ideal.span_singleton_mul_span_singleton, ih.symm],
end

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

--The following lemmas should be replaced by instances once we have an appropriate class
lemma ne.fact_coe (K R : Type*) (n : ℕ+) [field K] [ring R] [nontrivial R] [algebra K R]
  [hK : fact (((n : ℕ) : K) ≠ 0)] : fact (((n : ℕ) : R) ≠ 0) :=
⟨by simpa using (function.injective.ne (algebra_map K R).injective hK.out)⟩

lemma ne.fact_char_zero (K : Type*) (n : ℕ+) [field K] [char_zero K] :
  fact (((n : ℕ) : K) ≠ 0) := ⟨nat.cast_ne_zero.mpr n.pos.ne'⟩

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

@[simp]
lemma zeta'_pow_prime : (zeta' n A B) ^ (n : ℕ) = 1 :=
begin
  suffices : is_root (X ^ (n : ℕ) - 1) (zeta' n A B),
  { simpa [sub_eq_zero] using this },
  refine is_root.dvd _ cyclotomic.dvd_X_pow_sub_one,
  apply zeta'_spec'
end

lemma zeta'_primitive_root [is_domain B] [hn : fact (((n : ℕ) : B) ≠ 0)] :
  is_primitive_root (zeta' n A B) n :=
begin
  rw ←is_root_cyclotomic_iff,
  convert zeta'_spec' n A B,
  exact hn.out,
end

section field

variables [is_cyclotomic_extension {n} K L] [fact $ ((n : ℕ) : L) ≠ 0]

omit A

/-- The `power_basis` given by `zeta' n K L`. -/
-- this indentation is horrific.
def zeta'.power_basis : power_basis K L :=
power_basis.map
  (algebra.adjoin.power_basis $ integral {n} K L $ zeta' n K L) $
  (subalgebra.equiv_of_eq _ _
    (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ $ zeta'_primitive_root n K L)).trans
      algebra.top_equiv

-- after #11018 `simps gen` (maybe also with `simp_rhs:=tt`) will make this.
@[simp] lemma zeta'.power_basis_gen : (zeta'.power_basis n K L).gen = zeta' n K L := rfl

local attribute [instance] ne.fact_coe

/-- `zeta'.embeddings_equiv_primitive_roots` is the equiv between `B →ₐ[A] C` and
  `primitive_roots n C` given by the choice of `zeta'`. -/
@[simps]
def zeta'.embeddings_equiv_primitive_roots (A K C : Type*) [field A] [field K] [algebra A K]
  [is_cyclotomic_extension {n} A K] [comm_ring C] [algebra A C] [is_domain C] [algebra K C]
  [fact $ ((n : ℕ) : K) ≠ 0] (hirr : irreducible (cyclotomic n A)) :
  (K →ₐ[A] C) ≃ primitive_roots n C :=
have hn : fact (((n : ℕ) : C) ≠ 0) := infer_instance,
have hcyclo : minpoly A (zeta'.power_basis n A K).gen = cyclotomic n A :=
(minpoly.eq_of_irreducible_of_monic hirr
  (by rw [zeta'.power_basis_gen, zeta'_spec]) $ cyclotomic.monic n A).symm,
have h : ∀ x, (aeval x) (minpoly A (zeta'.power_basis n A K).gen) = 0 ↔ (cyclotomic n C).is_root x :=
λ x, by rw [aeval_def, eval₂_eq_eval_map, hcyclo, map_cyclotomic, is_root.def],
((zeta'.power_basis n A K).lift_equiv).trans
{ to_fun := λ x, ⟨x.1, by { rw [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff hn.out, ←h], exact x.2 }⟩,
  inv_fun := λ x, ⟨x.1, begin rw [h, is_root_cyclotomic_iff hn.out, ←mem_primitive_roots n.pos], exact x.2 end⟩,
  left_inv := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

-- the simp lemma that used to be below is now made by `simps`.

-- TODO use the fact that a primitive root is a unit.
-- TODO prove in general that is_primitive root is integral,
-- this exists as is_primitive_root.is_integral so use

end field

end is_cyclotomic_extension

namespace cyclotomic_ring

variables [is_domain A] [algebra A K] [is_fraction_ring A K] [fact (((n : ℕ) : K) ≠ 0)]

open is_cyclotomic_extension

lemma zeta'_integral :
  zeta' n K (cyclotomic_field n K) ∈ ring_of_integers (cyclotomic_field n K) :=
begin
  show is_integral ℤ (zeta' n _ _),
  use [cyclotomic n ℤ, cyclotomic.monic n ℤ],
  rw [← zeta'_spec n K (cyclotomic_field n K)],
  simp [aeval_def, eval₂_eq_eval_map],
end

local attribute [instance] cyclotomic_field.algebra_base

--zeta' should be in `(cyclotomic_ring n A K)` by definition.
lemma zeta'_mem_base : ∃ (x : (cyclotomic_ring n A K)), algebra_map
  (cyclotomic_ring n A K) (cyclotomic_field n K) x = zeta' n K (cyclotomic_field n K) :=
begin
  letI := classical.prop_decidable,
  let μ := zeta' n K (cyclotomic_field n K),
  haveI : fact (((n : ℕ) : cyclotomic_field n K) ≠ 0) := sorry, -- waiting for `ne_zero`
  have hμ := zeta'_primitive_root n K (cyclotomic_field n K),
  refine ⟨⟨μ, _⟩, rfl⟩,
  have := is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots n ⟨μ, hμ⟩,
  simp only [set.mem_singleton_iff, exists_eq_left] at this,
  rw [← this, is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic n μ hμ],
  apply algebra.subset_adjoin,
  exact set.mem_singleton _
end

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

local attribute [instance] ne.fact_coe
local attribute [instance] ne.fact_char_zero

/- set_option profiler true
set_option trace.class_instances true -/

-- there is some TC hell going on here. I think there's two algebras from `ring_of_integers blah`
-- to `blah`, and to boot they're also not defeq. Also, if I don't put the `no_zero_smul_divisors`
-- explicitly, this just flat-out refuses to compile in my VSCode (although it DOES! in the same
-- computer, when running through `leanproject build`). I'm really not sure what it is, but
-- I'm trying some band-aids for now and will ask people who know better on the Zulip. ~Eric
lemma zeta_primitive_root :
  is_primitive_root (zeta n K : ring_of_integers (cyclotomic_field n K)) n :=
begin
  let hf : function.injective (algebra_map (ring_of_integers (cyclotomic_field n K)) (cyclotomic_field n K)) :=
    by convert @no_zero_smul_divisors.algebra_map_injective (ring_of_integers $ cyclotomic_field n K)
      (cyclotomic_field n K) _ _ _ _
      (subalgebra.no_zero_smul_divisors_top (ring_of_integers $ cyclotomic_field n K)),
  apply is_primitive_root.of_map_of_injective hf,
  apply zeta'_primitive_root n _ _; apply_instance
end

set_option trace.class_instances false
set_option profiler false

lemma zeta_pow_eq_one : (zeta n K) ^ (n : ℕ) = 1 :=
by { ext, simp [zeta] }

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

lemma exists_unit_mul_primitive_root_one_sub_zeta (z : RR) (hz : is_primitive_root z n) :
  ∃ u : units RR, ↑u * (1 - z : RR) = 1 - (zeta n K) :=
begin
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
  rw ← fractional_ideal.span_singleton_pow,
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
