import ring_theory.adjoin.power_basis
import algebra.char_p.algebra

import number_theory.discriminant.basic
import number_theory.cyclotomic.cyclotomic_units
import ready_for_mathlib.nat
import ready_for_mathlib.cyclotomic

universes u v

open is_cyclotomic_extension algebra finset nat polynomial

open_locale big_operators

variables (K : Type u) [field K] [char_zero K] (p : ℕ+) [is_cyclotomic_extension {p} ℚ K]

local notation `pb` := zeta'.power_basis p ℚ K
local notation `ζ` := zeta' p ℚ K

lemma norm_zeta'_sub_one [hp : fact (p : ℕ).prime] (hodd : p ≠ 2) : norm ℚ (ζ - 1) = p :=
begin
  let E := algebraic_closure ℚ,
  letI := char_zero_of_injective_algebra_map (algebra_map ℚ E).injective,
  have hpE : ((p : ℕ) : E) ≠ 0 := λ h, p.pos.ne (cast_eq_zero.1 h).symm,
  obtain ⟨z, hz⟩ := is_alg_closed.exists_root _ (degree_cyclotomic_pos p E p.pos).ne.symm,

  apply (algebra_map ℚ E).injective,
  rw [norm_eq_prod_embeddings],
  conv_lhs { congr, skip, funext,
    rw [← neg_sub, alg_hom.map_neg, alg_hom.map_sub, alg_hom.map_one, neg_eq_neg_one_mul] },
  replace hodd : (p : ℕ) ≠ 2,
  { intro h,
    have : ((2 : ℕ+) : ℕ) = 2 := by rw [pnat.coe_bit0, pnat.one_coe],
    rw [← this, pnat.coe_inj] at h,
    exact hodd h },
  rw [prod_mul_distrib, prod_const, card_univ, alg_hom.card, singleton_finrank p,
    totient_prime hp.out, neg_one_pow_of_even (even_of_prime_neq_two_sub_one hp.out hodd), one_mul],
  have : univ.prod (λ (σ : K →ₐ[ℚ] E), 1 - σ (zeta' p ℚ K)) = eval 1 (cyclotomic' p E),
  { rw [cyclotomic', eval_prod, ← @finset.prod_attach E E, ← univ_eq_attach],
    exact fintype.prod_equiv (zeta'.embeddings_equiv_primitive_roots p ℚ K E) _ _ (λ σ, by simp) },
  rw [this, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitive_roots
    ((is_root_cyclotomic_iff hpE).2 hz), eval_one_cyclotomic_prime],
  simp,
end
