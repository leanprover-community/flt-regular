import ring_theory.polynomial.cyclotomic.basic

import ready_for_mathlib.polynomial

universe u

variables {R : Type u} [comm_ring R]

namespace polynomial

open_locale polynomial big_operators

open finset nat

lemma cyclotomic_comp_X_add_one (p : ℕ) [hp : fact p.prime] :
  (cyclotomic p R).comp (X + 1) = (range p).sum (λ (i : ℕ), X ^ i * p.choose (i + 1)) :=
begin
  have := cyclotomic_prime_mul_X_sub_one R p,
  replace this := congr_arg (λ P : R[X], P.comp (X + 1)) this,
  simp only [add_pow, mul_comp, sub_comp, X_comp, one_comp, add_sub_cancel, pow_comp, one_pow,
      mul_one] at this,
  rw [← insert_erase (show 0 ∈ finset.range (p + 1), by simp), sum_insert
      (not_mem_erase 0 _), pow_zero, one_mul, choose_zero_right, cast_one,
      add_sub_cancel'] at this,
  set f : ℕ → R[X] := λ i, X ^ i * (p.choose i) with hf,
  have aux : ∀ i ∈ (range (p + 1)).erase 0, f i = X * X ^ i.pred * (p.choose i),
  { intros i hi,
    simp only [mem_erase, ne.def, mem_range] at hi,
    simp only [← pow_succ, hf],
    congr,
    exact (succ_pred_eq_of_pos (zero_lt_iff.2 hi.1)).symm },
  simp_rw [finset.sum_congr rfl aux, mul_assoc, ← mul_sum, mul_comm _ X] at this,
  rw [mul_X_injective this],
  have miao := mul_X_injective this,
  refine finset.sum_bij (λ a _, a.pred) (λ a ha, _) (λ a ha, _) (λ a b ha hb hab, _) (λ a ha, _),
  { simp only [mem_erase, ne.def, mem_range] at ha,
    have := ha.2,
    rw [← succ_pred_eq_of_pos (zero_lt_iff.2 ha.1)] at this,
    exact mem_range.2 (succ_lt_succ_iff.1 this) },
  { simp only [mem_erase, ne.def, mem_range] at ha,
    congr,
    exact (succ_pred_eq_of_pos (zero_lt_iff.2 ha.1)).symm },
  { simp only [mem_erase, ne.def, mem_range] at ha,
    simp only [mem_erase, ne.def, mem_range] at hb,
    refine pred_inj (zero_lt_iff.2 ha.1) (zero_lt_iff.2 hb.1) hab },
  { refine ⟨a.succ, _, nat.pred_succ _⟩,
    simp only [mem_erase, ne.def, mem_range] at ha,
    simp only [mem_erase, ne.def, succ_ne_zero, not_false_iff, mem_range, true_and],
    exact succ_lt_succ_iff.2 ha }
end

end polynomial
