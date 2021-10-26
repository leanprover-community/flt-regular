import ring_theory.class_group
import number_theory.regular_primes



theorem flt_regular_case_one (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (hpne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p.coprime (a * b * c)) : a * b * c = 0 :=
sorry

theorem flt_regular_case_two (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (hpne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p ∣ a * b * c) : a * b * c = 0 := sorry

theorem flt_regular (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p) (hpne_two : p ≠ 2)
  (h : a ^ p + b ^ p = c ^ p) : a * b * c = 0 :=
begin
  by_cases hpabc : p ∣ a * b * c,
  exact flt_regular_case_two p a b c hp hpne_two h hpabc,
  have : p.coprime (a * b * c),
  refine (nat.prime.coprime_iff_not_dvd (fact.out _)).mpr hpabc,
  exact flt_regular_case_one p a b c hp hpne_two h this,
end
