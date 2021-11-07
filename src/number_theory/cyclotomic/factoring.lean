/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import number_theory.cyclotomic.basic
import number_theory.cyclotomic.cyclotomic_units
import number_theory.cyclotomic.absolute_value


universes u v
variables (A : Type u) (B : Type v)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables (n : ℕ+) [is_cyclotomic_extension {n} A B]

open_locale big_operators
open finset is_cyclotomic_extension
local notation `ζ` := zeta' n A B


open polynomial
-- lemma X_pow_sub_one_eq_prod {ζ : K} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) :
--   X ^ n - 1 = ∏ ζ in nth_roots_finset n K, (X - C ζ) :=
-- begin
--   rw [nth_roots_finset, ← multiset.to_finset_eq (is_primitive_root.nth_roots_nodup h)],
--   simp only [finset.prod_mk, ring_hom.map_one],
--   rw [nth_roots],
--   have hmonic : (X ^ n - C (1 : K)).monic := monic_X_pow_sub_C (1 : K) (ne_of_lt hpos).symm,
--   symmetry,
--   apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic,
--   rw [@nat_degree_X_pow_sub_C K _ _ n 1, ← nth_roots],
--   exact is_primitive_root.card_nth_roots h
-- end
/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n + y^n = ∏ (X + μ y)`, where `μ`
varies over the `n`-th roots of unity. -/
lemma pow_add_pow_eq_prod_add_zeta_mul [nontrivial B] (x y : B) :
  x ^ (n : ℕ) - y ^ (n : ℕ) = ∏ i in range n, (x - ζ ^ i * y) :=
begin
  suffices : (X : polynomial B) ^ (n : ℕ) - C y ^ (n : ℕ) = ∏ i in range n, (X - C (ζ ^ i * y)),
  { apply_fun (eval x) at this,
    simpa [eval_prod] using this, },
  ext,
  rw prod_X_sub_C_coeff,
  simp_rw prod_mul_distrib,
  simp_rw prod_const,
  conv in (y ^ (card _))
  { rw (mem_powerset_len.mp H).2, },
  rw ← sum_mul,
  rw ← mul_assoc,
  rw ← prod_X_sub_C_coeff,
  sorry,
  sorry,
  sorry,
  -- rw is_primitive_root.card_nth_roots_finset,
  -- rw ← X_pow_sub_one_eq_prod,
  -- -- rw [nth_roots_finset, ← multiset.to_finset_eq (is_primitive_root.nth_roots_nodup h)],
  -- simp only [finset.prod_mk, ring_hom.map_one],
  -- rw [nth_roots],
  -- have hmonic : (X ^ n - C (1 : K)).monic := monic_X_pow_sub_C (1 : K) (ne_of_lt hpos).symm,
  -- symmetry,
  -- apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic,
  -- rw [@nat_degree_X_pow_sub_C K _ _ n 1, ← nth_roots],
  -- exact is_primitive_root.card_nth_roots h
end
