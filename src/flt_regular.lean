import ring_theory.class_group
import number_theory.regular_primes
import tactic.may_assume
import data.zmod.extras
import tactic
import data.nat.prime_extras

lemma flt_coprime (p a b c : ℕ) [fact p.prime] (h : a ^ p + b ^ p = c ^ p) (hab: a.coprime b)
    : b.coprime c ∧  a.coprime c := sorry

lemma flt_three_case_one_aux {A B C : zmod 9} (h : A ^ 3 + B ^ 3 = C ^ 3) : 3 ∣ A * B * C :=
by revert A B C; dec_trivial

theorem flt_regular_case_one (p a b c : ℕ) [h_prime : fact p.prime] (hp : is_regular_number p)
  (hp_ne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p.coprime (a * b * c)) : false :=
begin
  by_cases hp_three : p = 3,
  { simp only [hp_three] at *,
    suffices : 3 ∣ a * b * c,
    { rw nat.prime.dvd_iff_not_coprime (by norm_num : nat.prime 3) at this,
      exact this hpabc, },
    have : (a : zmod 9) ^ 3 + b ^ 3 = c ^ 3,
    { rw_mod_cast h, },
    have := flt_three_case_one_aux this,
    norm_cast at this,
    convert dvd_of_dvd_zmod (by norm_num : 3 ∣ 9) (by exact_mod_cast this), },
  { have hp_five : 5 ≤ p, from h_prime.elim.five_le hp_ne_two hp_three,
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
