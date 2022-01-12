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
import ready_for_mathlib.ring_of_integers
import ready_for_mathlib.ideal_stuff
import ready_for_mathlib.roots_of_unity

noncomputable theory

open_locale big_operators non_zero_divisors
open number_field polynomial finset module units fractional_ideal submodule

universe variables u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

local notation `𝓞` := number_field.ring_of_integers

namespace is_cyclotomic_extension

variables [is_cyclotomic_extension {n} A B]

include A n
/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
def zeta : B := (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0).some

@[simp] lemma zeta_spec : aeval (zeta n A B) (cyclotomic n A) = 0 :=
classical.some_spec (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

lemma zeta_spec' : is_root (cyclotomic n B) (zeta n A B) :=
by { convert zeta_spec n A B, rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic] }

lemma zeta_primitive_root [is_domain B] [ne_zero ((n : ℕ) : B)] :
  is_primitive_root (zeta n A B) n :=
by { rw ←is_root_cyclotomic_iff, exact zeta_spec' n A B }

-- how do I get `simps` to make the `coe_inv_coe` lemma? `coe_inv_coe` doesn't work#
/-- `zeta n A B` as a member of the `roots_of_unity` subgroup. -/
@[simps coe_coe] def zeta_runity : roots_of_unity n B :=
roots_of_unity.mk_of_pow_eq (zeta n A B) $
is_root_of_unity_of ((n : ℕ).mem_divisors_self n.ne_zero) $ zeta_spec' n A B

/-- `zeta n A B` as a member of `Bˣ`. -/
@[simps] def zeta_unit : Bˣ := zeta_runity n A B

lemma coe_zeta_runity_unit : ↑(zeta_runity n A B) = zeta_unit n A B := rfl

lemma zeta_pow : (zeta n A B) ^ (n : ℕ) = 1 :=
by simpa using congr_arg (coe : Bˣ → B) ((mem_roots_of_unity _ _).mp (zeta_runity n A B).2)

section field

variables [is_cyclotomic_extension {n} K L] [ne_zero ((n : ℕ) : K)]

omit A

/-- The `power_basis` given by `zeta n K L`. -/
-- this indentation is horrific, and I do not know why term mode doesn't want to work...
@[simps] def zeta.power_basis : power_basis K L :=
begin
haveI : ne_zero ((n : ℕ) : L) := ne_zero.of_no_zero_smul_divisors K L,
refine power_basis.map
  (algebra.adjoin.power_basis $ integral {n} K L $ zeta n K L) _,
exact (subalgebra.equiv_of_eq _ _
      (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ $ zeta_primitive_root n K L)).trans
      algebra.top_equiv
end

/-- `zeta.embeddings_equiv_primitive_roots` is the equiv between `B →ₐ[A] C` and
  `primitive_roots n C` given by the choice of `zeta`. -/
@[simps]
def zeta.embeddings_equiv_primitive_roots (A K C : Type*) [field A] [field K] [algebra A K]
  [is_cyclotomic_extension {n} A K] [comm_ring C] [is_domain C] [algebra A C]
  [ne_zero ((n : ℕ) : A)] (hirr : irreducible (cyclotomic n A)) :
  (K →ₐ[A] C) ≃ primitive_roots n C :=
have hn : ne_zero ((n : ℕ) : C) := ne_zero.of_no_zero_smul_divisors A C,
have hcyclo : minpoly A (zeta.power_basis n A K).gen = cyclotomic n A :=
(minpoly.eq_of_irreducible_of_monic hirr
  (by rw [zeta.power_basis_gen, zeta_spec]) $ cyclotomic.monic n A).symm,
have h : ∀ x, (aeval x) (minpoly A (zeta.power_basis n A K).gen) = 0 ↔ (cyclotomic n C).is_root x :=
λ x, by rw [aeval_def, eval₂_eq_eval_map, hcyclo, map_cyclotomic, is_root.def],
((zeta.power_basis n A K).lift_equiv).trans
{ to_fun    := λ x, ⟨x.1, by { casesI x, rwa [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff, ←h] }⟩,
  inv_fun   := λ x, ⟨x.1, by { casesI x, rwa [h, is_root_cyclotomic_iff, ←mem_primitive_roots n.pos] }⟩,
  left_inv  := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

end field

end is_cyclotomic_extension

namespace cyclotomic_ring

variables [is_domain A] [algebra A K] [is_fraction_ring A K] [ne_zero ((n : ℕ) : K)]

open is_cyclotomic_extension

lemma zeta_integral :
  zeta n K (cyclotomic_field n K) ∈ 𝓞 (cyclotomic_field n K) :=
begin
  use [cyclotomic n ℤ, cyclotomic.monic n ℤ],
  rw [← zeta_spec n K (cyclotomic_field n K)],
  simp [aeval_def, eval₂_eq_eval_map],
end

local attribute [instance] cyclotomic_field.algebra_base

--zeta should be in `(cyclotomic_ring n A K)` by definition.
lemma zeta_mem_base : ∃ (x : (cyclotomic_ring n A K)), algebra_map
  (cyclotomic_ring n A K) (cyclotomic_field n K) x = zeta n K (cyclotomic_field n K) :=
begin
  have : ne_zero ((n : ℕ) : cyclotomic_field n K) := ne_zero.of_no_zero_smul_divisors K _,
  letI := classical.prop_decidable,
  let μ := zeta n K (cyclotomic_field n K),
  have hμ := zeta_primitive_root n K (cyclotomic_field n K),
  refine ⟨⟨μ, _⟩, rfl⟩,
  have := is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots n hμ,
  simp only [set.mem_singleton_iff, exists_eq_left] at this,
  rw [← this, is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic n μ hμ],
  exact algebra.subset_adjoin (set.mem_singleton _),
end

open is_cyclotomic_extension

section cyclotomic_unit

variable {n}

local notation `RR` := ring_of_integers (cyclotomic_field n K)
local notation `L` := cyclotomic_field n K


namespace cyclotomic_unit

/-

-- maybe this should use `smul` or something to avoid the horrific typleclass issues that have
-- been going on here
lemma exists_unit_mul_primitive_root_one_sub_zeta_runity (z : RR) (hz : is_primitive_root z n) :
  ∃ u : RRˣ, ↑u * (1 - z : RR) = 1 - (zeta_runity n (𝓞 K) (𝓞 L)) :=
begin
  sorry
  -- haveI asda : fact (((n : ℕ) : 𝓞 L) ≠ 0) := sorry, resetI,
  -- rw is_primitive_root.is_primitive_root_iff ((@zeta_primitive_root n (𝓞 K) (𝓞 L) _ _ _ _ _ asda))
  --   n.pos at hz,
  -- obtain ⟨i, hip, hin, hi⟩ := hz,
  -- rw ← hi,
  -- refine ⟨(cyclotomic_unit K (nat.gcd_one_left _) hin), _⟩,
  -- rw ← neg_sub,
  -- rw mul_neg_eq_neg_mul_symm,
  -- simp [mul_denom K (nat.gcd_one_left _) hin],
end

variable (n)

instance : is_localization ((ring_of_integers (cyclotomic_field n K)))⁰ (cyclotomic_field n K) :=
sorry

lemma prime_ideal_eq_pow_cyclotomic [hn : fact ((n : ℕ).prime)] :
  (span_singleton _ n : fractional_ideal RR⁰ L) =
  (span_singleton _ (1 - (zeta_runity n K L)) ^ ((n : ℕ) - 1) : fractional_ideal RR⁰ L) :=
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
  --    cyclotomic_eq_prod_X_sub_primitive_roots (zeta_primitive_root n _)
  --                      ... = _ : by simp only [polynomial.eval_sub, polynomial.eval_C,
  --                                  polynomial.eval_prod, polynomial.eval_X],

  -- apply span_singleton_eq_span_singleton_,
  sorry,
end -/

end cyclotomic_unit

end cyclotomic_unit

end cyclotomic_ring
