import ring_theory.class_group
import number_theory.regular_primes
import tactic.may_assume
import tactic.omega
import tactic

lemma flt_coprime (p a b c : ℕ) [fact p.prime] (h : a ^ p + b ^ p = c ^ p) (hab: a.coprime b)
    : b.coprime c ∧  a.coprime c := sorry

lemma flt_three_case_one_aux {A B C : zmod 9} (h : A ^ 3 + B ^ 3 = C ^ 3) : 3 ∣ A * B * C :=
by revert A B C; dec_trivial

lemma zmod.nat_coe_eq_nat_coe_iff' (a b c : ℕ) :
  (a : zmod c) = (b : zmod c) ↔ a % c = b % c :=
zmod.nat_coe_eq_nat_coe_iff a b c

-- TODO wow another horrible proof
lemma dvd_of_dvd_zmod {m n a : ℕ} (hmn : m ∣ n) (h : (m : zmod n) ∣ a) : m ∣ a :=
begin
  rcases n with r | n,
  { simp only [int.nat_cast_eq_coe_nat] at h,
    exact_mod_cast h, },
  rcases hmn with ⟨hmn_w, hmn_h⟩,
  rcases h with ⟨⟨h_w_val, h_w_property⟩, h_h⟩,
  rw (_ : (m : zmod (n + 1)) * ⟨h_w_val, h_w_property⟩ = ↑(m * h_w_val)) at h_h,
  rw zmod.nat_coe_eq_nat_coe_iff' at h_h,
  rw hmn_h at h_h,
  cases le_total a (m * h_w_val),
  focus { symmetry' at h_h, },
  { have := nat.dvd_of_mod_eq_zero (nat.sub_mod_eq_zero_of_mod_eq h_h),
    have : m ∣ m * h_w_val - a := dvd_trans (dvd.intro hmn_w rfl) this,
    rw nat.dvd_iff_mod_eq_zero at this,
    zify at this,
    simp at this,
    have hok : (m : ℤ) ∣ ↑m * ↑h_w_val,
    exact dvd.intro ↑h_w_val rfl,
    have : (m : ℤ) ∣ ↑m * ↑h_w_val - a - ↑m * ↑h_w_val,
    exact dvd_sub this hok,
    simp at this,
    exact int.coe_nat_dvd.mp this, },
  { have := nat.dvd_of_mod_eq_zero (nat.sub_mod_eq_zero_of_mod_eq h_h),
    have : m ∣ a - m * h_w_val := dvd_trans (dvd.intro hmn_w rfl) this,
    rw nat.dvd_iff_mod_eq_zero at this,
    rw nat.sub_mul_mod _ _ _ h at this,
    exact nat.dvd_of_mod_eq_zero this, },
  rw [nat.cast_mul],
  congr,
  ext,
  simp [nat.mod_eq_of_lt h_w_property],
end

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
    convert dvd_of_dvd_zmod (by norm_num : 3 ∣ 9) (by exact_mod_cast this), },
  { have hp_five : 5 ≤ p,
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
