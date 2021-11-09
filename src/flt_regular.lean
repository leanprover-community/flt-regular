import ring_theory.class_group
import number_theory.regular_primes
import tactic.may_assume
import data.zmod.extras
import tactic
import data.nat.prime_extras
import ready_for_mathlib.totient

lemma flt_coprime (p a b c : ℕ) [fact p.prime] (h : a ^ p + b ^ p = c ^ p) (hab: a.coprime b)
    : b.coprime c ∧ a.coprime c := sorry

lemma flt_three_case_one_aux {A B C : zmod 9} (h : A ^ 3 + B ^ 3 = C ^ 3) : 3 ∣ A * B * C :=
by sorry --revert A B C ; dec_trivial

theorem flt_regular_case_one (p a b c : ℕ) [h_prime : fact p.prime] (hp : is_regular_number p)
  (hp_ne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p.coprime (a * b * c)) : false :=
begin
  unfreezingI { rcases eq_or_ne p 3 with rfl | hp_three },
  { suffices : 3 ∣ a * b * c,
    { exact (nat.prime_three.dvd_iff_not_coprime.mp this) hpabc, },
    have : (a : zmod 9) ^ 3 + b ^ 3 = c ^ 3,
    { rw_mod_cast h },
    convert dvd_of_dvd_zmod (by norm_num : 3 ∣ 9) (by exact_mod_cast flt_three_case_one_aux this) },
  { have hp_five : 5 ≤ p, from h_prime.elim.five_le hp_ne_two hp_three,
    sorry }
end

theorem flt_regular_case_two (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p)
  (hpne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p ∣ a * b * c) : a * b * c = 0 := sorry

theorem flt_regular (p a b c : ℕ) [fact p.prime] (hp : is_regular_number p) (hpne_two : p ≠ 2)
  (h : a ^ p + b ^ p = c ^ p) : a * b * c = 0 :=
begin
  may_assume hcoprime : set.pairwise {a, b, c} nat.coprime,
  { let d : ℕ := finset.gcd {a, b, c} id,
    specialize h_red p (a/d) (b/d) (c/d) ‹_› hp hpne_two _ _,
    { have habc := congr_arg (/ d^p) h,
      simp only at habc,
      rw nat.add_div (sorry /- 0 < d, finset.gcd api! (requires nonempty set) -/) at habc,
      have : ite (d ^ p ≤ a ^ p % d ^ p + b ^ p % d ^ p) 1 0 = 0,
      { simp only [nat.one_ne_zero, ite_eq_right_iff, imp_false, not_le],
        -- a ^ p % d ^ p + b ^ p % d ^ p < d ^ p, does this maybe only hold in case one?
        -- I haven't read the proof for case two, so I'm not sure if this requires coprimeness
        sorry },
      -- lifting arguments and d ∣ x (`finset.gcd_dvd`) should do quick work of this
      have key : ∀ x ∈ ({a, b, c} : set ℕ), x ^ p / d ^ p = (x / d) ^ p := sorry,
      simpa only [this, key, set.mem_insert_iff, set.mem_singleton_iff,
                  true_or, eq_self_iff_true, or_true] using habc },
    { sorry /- {a / d, b / d, c / d}.pairwise nat.coprime
               this should be a finset.gcd lemma, although has to be special-cased for ℕ :/ -/ },
    { have habc := congr_arg (* d^3) h_red,
      simp only [zero_mul] at habc,
      replace habc : (a / d * d) * (b / d * d) * (c / d * d) = 0,
      { convert habc using 1, ring },
      iterate 3 { rw nat.div_mul_cancel at habc },
      exact habc,
      all_goals { apply finset.gcd_dvd, simp } } },
  resetI, -- todo: will be fixed in may_assume
  cases nat.coprime_or_dvd_of_prime (fact.out p.prime) (a * b * c) with hpabc hpabc,
  { exact absurd hpabc (flt_regular_case_one p a b c hp hpne_two h) },
  { exact flt_regular_case_two p a b c hp hpne_two h hpabc }
end
