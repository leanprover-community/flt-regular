import ready_for_mathlib.roots_of_unity
import ring_theory.polynomial.cyclotomic.basic
import ready_for_mathlib.ne_zero

open is_primitive_root

namespace polynomial

lemma cyclotomic_mul_prime_not_dvd_eq_pow (R : Type*) {p n : ℕ} [hp : fact (nat.prime p)] [ring R]
  [char_p R p] (hn : ¬p ∣ n) : cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1) :=
begin
  suffices : cyclotomic (n * p) (zmod p) = (cyclotomic n (zmod p)) ^ (p - 1),
  { rw [← map_cyclotomic _ (algebra_map (zmod p) R), ← map_cyclotomic _ (algebra_map (zmod p) R),
      this, polynomial.map_pow] },
  suffices : cyclotomic (n * p) (zmod p) * (cyclotomic n (zmod p)) = (cyclotomic n (zmod p)) ^ p,
  { have h : cyclotomic n (zmod p) ^ p = cyclotomic n (zmod p) ^ p.pred.succ,
    { rw [nat.succ_pred_eq_of_pos hp.out.pos] },
    rw [h, pow_succ, mul_comm (cyclotomic (n * p) _)] at this,
    exact mul_right_injective₀ (cyclotomic_ne_zero _ _) this },
  rw [← zmod.expand_card],
  nth_rewrite 2 [← map_cyclotomic_int],
  rw [← map_expand, cyclotomic_expand_eq_cyclotomic_mul hp.out hn, polynomial.map_mul,
    map_cyclotomic, map_cyclotomic]
end

lemma cyclotomic_mul_prime_dvd_eq_pow (R : Type*) {p n : ℕ} [hp : fact (nat.prime p)] [ring R]
  [char_p R p] (hn : p ∣ n) : cyclotomic (n * p) R = (cyclotomic n R) ^ p :=
begin
  suffices : cyclotomic (n * p) (zmod p) = (cyclotomic n (zmod p)) ^ p,
  { rw [← map_cyclotomic _ (algebra_map (zmod p) R), ← map_cyclotomic _ (algebra_map (zmod p) R),
      this, polynomial.map_pow] },
  rw [← zmod.expand_card, ← map_cyclotomic_int n, ← map_expand, cyclotomic_expand_eq_cyclotomic
    hp.out hn, map_cyclotomic, mul_comm]
end

lemma cyclotomic_mul_prime_pow_eq (R : Type*) {p m k : ℕ} [hp : fact (nat.prime p)] [ring R]
  [char_p R p] (hk : 0 < k) (hm : ¬p ∣ m) :
  cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1)) :=
begin
  obtain ⟨a, ha⟩ := nat.exists_eq_succ_of_ne_zero hk.ne',
  rw [ha],
  clear ha hk,
  induction a with a H,
  { rw [pow_one, nat.sub_self, pow_zero, mul_comm, cyclotomic_mul_prime_not_dvd_eq_pow R hm] },
  { have hdiv : p ∣ p ^ a.succ * m := ⟨p ^ a * m, by rw [← mul_assoc, pow_succ]⟩,
    rw [pow_succ, mul_assoc, mul_comm, cyclotomic_mul_prime_dvd_eq_pow R hdiv, H, ← pow_mul],
    congr' 1,
    simp only [tsub_zero, nat.succ_sub_succ_eq_sub],
    rw [nat.mul_sub_right_distrib, mul_comm, pow_succ']  }
end

lemma is_root_cyclotomic_iff_char_zero {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  [char_zero R] {μ : R} [hn : ne_zero n] :
  (polynomial.cyclotomic n R).is_root μ ↔ is_primitive_root μ n :=
by exactI ⟨λ h, is_root_cyclotomic_iff.1 h, λ h, is_root_cyclotomic hn.out.bot_lt h⟩

lemma is_root_cyclotomic_iff_char_p {m k p : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  [hp : fact (nat.prime p)] [hchar : char_p R p] {μ : R} [ne_zero (m : R)] :
  (polynomial.cyclotomic (p ^ k * m) R).is_root μ ↔ is_primitive_root μ m :=
begin
  rcases k.eq_zero_or_pos with rfl | hk,
  { rw [pow_zero, one_mul, is_root_cyclotomic_iff] },
  refine ⟨λ h, _, λ h, _⟩,
  { rw [is_root.def, cyclotomic_mul_prime_pow_eq R hk (ne_zero.not_dvd_char R m), eval_pow] at h,
    replace h := pow_eq_zero h,
    rwa [← is_root.def, is_root_cyclotomic_iff] at h,
    all_goals {apply_instance} },
  { rw [← is_root_cyclotomic_iff, is_root.def] at h,
    rw [cyclotomic_mul_prime_pow_eq R hk (ne_zero.not_dvd_char R m),
        is_root.def, eval_pow, h, zero_pow],
    simp only [tsub_pos_iff_lt],
    exact strict_mono_pow hp.out.one_lt (buffer.lt_aux_2 hk),
    all_goals {apply_instance} }
end

end polynomial
