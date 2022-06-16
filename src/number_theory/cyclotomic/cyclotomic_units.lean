/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import number_theory.cyclotomic.primitive_roots
import ring_theory.polynomial.cyclotomic.eval

import ready_for_mathlib.ideal_stuff

import tactic.may_assume
import number_theory.pnat

noncomputable theory

open_locale big_operators non_zero_divisors number_field pnat
open number_field polynomial finset module units fractional_ideal submodule

universe variables u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

namespace is_primitive_root

variable {B}

lemma is_integral' {n : ℕ} {μ : B} (hμ : is_primitive_root μ n) (hn : 0 < n) :
  _root_.is_integral A μ :=
begin
  use (X ^ n - 1),
  split,
  { exact (monic_X_pow_sub_C 1 (ne_of_lt hn).symm) },
  { simp only [((is_primitive_root.iff_def μ n).mp hμ).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self] }
end

variable (B)

end is_primitive_root

namespace is_cyclotomic_extension

variables [is_cyclotomic_extension {n} A B]

-- how do I get `simps` to make the `coe_inv_coe` lemma? `coe_inv_coe` doesn't work#
/-- `zeta n A B` as a member of the `roots_of_unity` subgroup. -/
@[simps coe_coe] def zeta_runity : roots_of_unity n B :=
roots_of_unity.mk_of_pow_eq (zeta n A B) $
is_root_of_unity_of_root_cyclotomic ((n : ℕ).mem_divisors_self n.ne_zero) $ zeta_spec' n A B

/-- `zeta n A B` as a member of `Bˣ`. -/
@[simps] def zeta_unit : Bˣ := zeta_runity n A B

lemma coe_zeta_runity_unit : ↑(zeta_runity n A B) = zeta_unit n A B := rfl

end is_cyclotomic_extension

namespace cyclotomic_ring

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

open is_cyclotomic_extension

lemma zeta_integral [is_cyclotomic_extension {n} K L] :
  zeta n K L ∈ 𝓞 L :=
begin
  use [cyclotomic n ℤ, cyclotomic.monic n ℤ],
  rw [← zeta_spec n K L],
  simp [aeval_def, eval₂_eq_eval_map],
end

lemma zeta_integral' [is_cyclotomic_extension {n} K L] (i : ℕ):
  (zeta n K L)^i ∈ 𝓞 L :=
begin
 apply subalgebra.pow_mem,
 apply zeta_integral,
end


local attribute [instance] cyclotomic_field.algebra_base

--zeta should be in `(cyclotomic_ring n A K)` by definition.
lemma zeta_mem_base  [ne_zero (⥉n : K)] : ∃ (x : (cyclotomic_ring n A K)), algebra_map
  (cyclotomic_ring n A K) (cyclotomic_field n K) x = zeta n K (cyclotomic_field n K) :=
begin
  have := ne_zero.of_no_zero_smul_divisors K (cyclotomic_field n K) n,
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

-- I don't want to bother Leo, but I wonder if this can be automated in Lean4
-- (if they were 0 < n → 1 < n, it would work already!)
lemma _root_.nat.one_lt_of_ne : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → 1 < n
| 0 h _ := absurd rfl h
| 1 _ h := absurd rfl h
| (n+2) _ _ := n.one_lt_succ_succ

-- this result holds for all primitive roots; dah.
lemma associated_one_sub_pow_primitive_root_of_coprime {n j k : ℕ} {ζ : A}
  (hζ : is_primitive_root ζ n) (hk : k.coprime n) (hj : j.coprime n) :
  associated (1 - ζ ^ j) (1 - ζ ^ k) :=
begin
  suffices : ∀ {j : ℕ}, j.coprime n → associated (1 - ζ) (1 - ζ ^ j),
  { exact (this hj).symm.trans (this hk) },
  clear' k j hk hj,
  refine λ j hj, associated_of_dvd_dvd ⟨∑ i in range j, ζ ^ i,
    by rw [← geom_sum_mul_neg, mul_comm]⟩ _,
  -- is there an easier way to do this?
  rcases eq_or_ne n 0 with rfl | hn',
  { simp [j.coprime_zero_right.mp hj] },
  rcases eq_or_ne n 1 with rfl | hn,
  { simp [is_primitive_root.one_right_iff.mp hζ] },
  replace hn := n.one_lt_of_ne hn' hn,
  obtain ⟨m, hm⟩ := nat.exists_mul_mod_eq_one_of_coprime hj hn,
  use (∑ i in range m, (ζ ^ j) ^ i),
  have : ζ = (ζ ^ j) ^ m,
  { rw [←pow_mul, pow_eq_mod_order_of, ←hζ.eq_order_of, hm, pow_one] },
  nth_rewrite 0 this,
  rw [← geom_sum_mul_neg, mul_comm]
end

lemma _root_.is_primitive_root.one_add_is_unit {n : ℕ} {ζ : A} (hζ : is_primitive_root ζ n)
  (hn : n ≠ 1) (hn': ¬ 2 ∣ n) : is_unit (1 + ζ) :=
begin
  have := (associated_one_sub_pow_primitive_root_of_coprime A hζ
            n.coprime_one_left (nat.prime_two.coprime_iff_not_dvd.mpr hn')),
  rw [pow_one, ← one_pow 2, sq_sub_sq, one_pow, mul_comm] at this,
  refine is_unit_of_associated_mul this (sub_ne_zero.mpr _),
  rintro rfl,
  exact hn (hζ.eq_order_of.trans order_of_one)
end

/-

variable (n)

instance : is_localization ((ring_of_integers (cyclotomic_field n K)))⁰ (cyclotomic_field n K) :=
admit

lemma prime_ideal_eq_pow_cyclotomic [hn : fact ((n : ℕ).prime)] :
  (span_singleton _ n : fractional_ideal RR⁰ L) =
  (span_singleton _ (1 - (zeta_runity n K L)) ^ ((n : ℕ) - 1) : fractional_ideal RR⁰ L) :=
  --(mk0 (p : cyclotomic_field p) (by norm_num [hn.ne_zero]))
begin
  rw fractional_ideal.span_singleton_pow,
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
  admit,
end -/

end cyclotomic_unit

end cyclotomic_unit

end cyclotomic_ring
