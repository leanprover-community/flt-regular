import ring_theory.class_group
import number_theory.regular_primes
import tactic.may_assume
import data.zmod.extras
import tactic
import data.nat.prime_extras
import algebra.gcd_monoid.nat
import number_theory.cyclotomic.factoring
import number_theory.cyclotomic.case_I

-- TODO I (alex) commented this out as it seems redundent now? -- agree, seems redundant - Eric
-- lemma flt_coprime (p a b c : ℕ) [fact p.prime] (h : a ^ p + b ^ p = c ^ p) (hab : a.coprime b)
--     : b.coprime c ∧ a.coprime c := admit

open polynomial fractional_ideal

open_locale non_zero_divisors number_field

/-- Case II (when a,b,c are not coprime to the exponent), of FLT for regular primes. -/
theorem flt_regular_case_two (p a b c : ℕ) (hp : p.prime) (hpreg : is_regular_number p hp.pos)
  (hpne_two : p ≠ 2) (h : a ^ p + b ^ p = c ^ p) (hpabc : p ∣ a * b * c) : a * b * c = 0 := sorry

theorem flt_regular (p a b c : ℕ) (hp : p.prime) (hpreg : is_regular_number p hp.pos) (hpne_two : p ≠ 2)
  (h : a ^ p + b ^ p = c ^ p) : a * b * c = 0 :=
begin
  sorry
  -- may_assume hcoprime : ({a, b, c} : finset ℕ).gcd id = 1,
  -- { let s : finset ℕ := {a, b, c},
  --   let d : ℕ := s.gcd id,
  --   rcases eq_or_ne c 0 with rfl | hc, --budget may_assume ;b needed for `image_div_gcd_coprime`
  --   { rw mul_zero },
  --   cases d.eq_zero_or_pos with hd hd,
  --   { rw finset.gcd_eq_zero_iff at hd,
  --     rw mul_eq_zero,
  --     exact or.inr (hd c $ by simp) },
  --   specialize h_red p (a/d) (b/d) (c/d) ‹_› hp hpne_two _ _,
  --   { have habc := congr_arg (/ d^p) h,
  --     simp only at habc,
  --     rw nat.add_div (pow_pos hd p) at habc,
  --     have : ite (d ^ p ≤ a ^ p % d ^ p + b ^ p % d ^ p) 1 0 = 0,
  --     { simp only [nat.one_ne_zero, ite_eq_right_iff, imp_false, not_le],
  --       convert pow_pos hd p,
  --       rw add_eq_zero_iff,
  --       split;
  --       { apply nat.mod_eq_zero_of_dvd,
  --         apply pow_dvd_pow_of_dvd,
  --         apply finset.gcd_dvd,
  --         simp } },
  --     have key : ∀ x ∈ ({a, b, c} : finset ℕ), x ^ p / d ^ p = (x / d) ^ p,
  --     { intros x xh,
  --       rw div_pow''', -- TODO move this lemma to a reasonable place / name and mathlib
  --       exact (finset.gcd_dvd xh), },
  --     simpa only [this, key, true_or, eq_self_iff_true, or_true, finset.mem_insert,
  --                 finset.mem_singleton] using habc },
  --   { convert s.coprime_of_div_gcd _ hc using 1,
  --     conv_rhs { rw finset.gcd_eq_gcd_image },
  --     congr,
  --     simp only [finset.image_insert, id.def, finset.image_singleton, normalize_eq],
  --     simp },
  --   { have habc := congr_arg (* d^3) h_red,
  --     simp only [zero_mul] at habc,
  --     replace habc : (a / d * d) * (b / d * d) * (c / d * d) = 0,
  --     { convert habc using 1, ring },
  --     iterate 3 { rw nat.div_mul_cancel at habc },
  --     exact habc,
  --     all_goals { apply finset.gcd_dvd, simp } } },
  -- cases nat.coprime_or_dvd_of_prime (fact.out p.prime) (a * b * c) with hpabc hpabc,
  -- { exact absurd hpabc (λ habs, sorry),
  --    --exact absurd hpabc (λ _, flt_regular_case_one hp hpne_two sorry hpabc h)
  --    },
  -- { exact flt_regular_case_two p a b c hp hpne_two h hpabc }
end
