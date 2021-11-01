import ring_theory.class_group
import number_theory.regular_primes
import tactic.may_assume

lemma flt_coprime (p a b c : ℕ) [fact p.prime] (h : a ^ p + b ^ p = c ^ p) (hab: a.coprime b)
    : b.coprime c ∧  a.coprime c := sorry

lemma flt_three_case_one_aux {A B C : zmod 9} (h : A ^ 3 + B ^ 3 = C ^ 3) : 3 ∣ A * B * C :=
by revert A B C; dec_trivial

theorem flt_regular_case_one (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (hpne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p.coprime (a * b * c)) : false :=
begin
  by_cases hp_three : p = 3,
  { haveI : fact (nat.prime 3) := fact.mk (by norm_num),
    simp only [hp_three] at *,
    suffices : 3 ∣ a * b * c,
    { rw nat.prime.dvd_iff_not_coprime (fact.out (nat.prime 3)) at this,
      exact this hpabc, },
    have : (a : zmod 9) ^ 3 + b ^ 3 = c ^ 3,
    rw_mod_cast h,
    have := flt_three_case_one_aux this,
    norm_cast at this,
    -- this should be a lemma!
    have h_dvd : 3 ∣ 9 := by norm_num,
    obtain ⟨f, hf⟩ := exists_eq_mul_right_of_dvd this,
    -- cases f,
    -- use f_val,
    sorry, },
  { have hp_five: 5 ≤ p,
    sorry,
    sorry }
end

theorem flt_regular_case_two (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (hpne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p ∣ a * b * c) : a * b * c = 0 := sorry

theorem flt_regular (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p) (hpne_two : p ≠ 2)
  (h : a ^ p + b ^ p = c ^ p) : a * b * c = 0 :=
begin
  by_cases hpabc : p ∣ a * b * c,
  exact flt_regular_case_two p a b c hp hpne_two h hpabc,
  have : p.coprime (a * b * c),
  refine (nat.prime.coprime_iff_not_dvd (fact.out _)).mpr hpabc,
  exfalso,
  exact flt_regular_case_one p a b c hp hpne_two h this,
end
