/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.polynomial.field_division
import number_theory.number_field
import ready_for_mathlib.cyclotomic.basic
import ring_theory.polynomial.cyclotomic.eval

import ready_for_mathlib.zeta
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

-- how do I get `simps` to make the `coe_inv_coe` lemma? `coe_inv_coe` doesn't work#
/-- `zeta n A B` as a member of the `roots_of_unity` subgroup. -/
@[simps coe_coe] def zeta_runity : roots_of_unity n B :=
roots_of_unity.mk_of_pow_eq (zeta n A B) $
is_root_of_unity_of ((n : ℕ).mem_divisors_self n.ne_zero) $ zeta_spec' n A B

/-- `zeta n A B` as a member of `Bˣ`. -/
@[simps] def zeta_unit : Bˣ := zeta_runity n A B

lemma coe_zeta_runity_unit : ↑(zeta_runity n A B) = zeta_unit n A B := rfl

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

-- I wonder if we can do these results after we have 𝓞 K is a cyclotomic extension;
-- or do they hold for anything with a primitive root?

lemma exists_unit_mul_primitive_root_one_sub_zeta_runity (z : 𝓞 L) (hz : is_primitive_root z n) :
  ∃ u : (𝓞 L)ˣ, ↑u * (1 - z : 𝓞 L) = 1 - ⟨zeta n K L, zeta_integral n K⟩ :=
begin
  haveI : ne_zero ((n : ℕ) : L) := sorry,
  rw is_primitive_root.is_primitive_root_iff
    (show is_primitive_root (⟨zeta n K L, zeta_integral n K⟩ : 𝓞 L) n, from _) n.pos at hz,
  swap,
  { have : is_primitive_root ((algebra_map (𝓞 L) L) ⟨zeta n K L, zeta_integral n K⟩) n :=
           zeta_primitive_root n K L,
    -- todo: i should change the argument order in mathlib
    refine is_primitive_root.of_map_of_injective _ this,
    exact subtype.val_injective },
  obtain ⟨i, hip, hin, hi⟩ := hz,
  rw ← hi,
  sorry; { refine ⟨(cyclotomic_unit K (nat.gcd_one_left _) hin), _⟩,
  rw ← neg_sub,
  rw mul_neg_eq_neg_mul_symm,
  simp [mul_denom K (nat.gcd_one_left _) hin] },
end

/-

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
