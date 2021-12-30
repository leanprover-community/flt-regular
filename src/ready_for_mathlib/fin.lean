import data.fin.interval
import algebra.big_operators.intervals

namespace fin

open finset

open_locale big_operators

lemma prod_filter_gt_mul_neg_eq_prod_off_diag {R : Type*} [comm_ring R] {n : ℕ}
  {f : fin n → fin n → R} (hf : ∀ i j, f j i = - f i j) :
  ∏ i, (∏ j in finset.univ.filter (λ j, i < j), (f j i) * (f i j)) =
  ∏ i, (∏ j in finset.univ.filter (λ j, i ≠ j), (f j i)) :=
begin
  simp_rw [ne_iff_lt_or_gt, or.comm, finset.filter_or],
  refine eq.trans _ (congr_arg (finset.prod _) (funext $ λ i, (finset.prod_union _).symm)),
  simp_rw [finset.prod_mul_distrib],
  { conv_rhs {
      congr, skip, congr, skip, funext,
      conv {
        congr, skip, funext,
        rw [hf, neg_eq_neg_one_mul] },
      rw [finset.prod_mul_distrib, finset.prod_const] },
    simp_rw [finset.prod_mul_distrib],
    rw [← mul_assoc],
    congr,
    conv_lhs {
      congr, skip, funext,
      conv {
        congr, skip, funext,
        rw [hf, neg_eq_neg_one_mul] },
      rw [finset.prod_mul_distrib, finset.prod_const] },
    simp_rw [finset.prod_mul_distrib],
    nth_rewrite 0 [mul_comm],
    congr' 1,
    rw [finset.prod_sigma', finset.prod_sigma'],
    exact finset.prod_bij' (λ i hi, ⟨i.2, i.1⟩) (by simp) (by simp) (λ i hi, ⟨i.2, i.1⟩)
      (by simp) (by simp) (by simp) },
  { rintro x hx,
    obtain ⟨⟨_, hl⟩, ⟨_, hg⟩⟩ := (finset.mem_inter.1 hx).imp finset.mem_filter.1 finset.mem_filter.1,
    exact (lt_asymm hl hg).elim, },
end


end fin
