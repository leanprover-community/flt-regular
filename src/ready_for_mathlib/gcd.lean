import algebra.gcd_monoid.finset
import number_theory.padics.padic_norm

lemma nat.ne_one_iff : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.prime ∧ p ∣ n
| 0 := by simpa using (Exists.intro 2 nat.prime_two) -- we need nat.prime_37 pronto ;b
| 1 := by simp [nat.not_prime_one]
| (n+2) :=
let a := n+2 in
let ha : a ≠ 1 := nat.succ_succ_ne_one n in
begin
  simp only [true_iff, ne.def, not_false_iff, ha],
  exact ⟨a.min_fac, nat.min_fac_prime ha, a.min_fac_dvd⟩,
end

lemma nat.eq_one_iff {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.prime → ¬p ∣ n :=
by simpa using not_iff_not.mpr nat.ne_one_iff

namespace finset

instance : is_idempotent ℕ gcd_monoid.gcd := ⟨nat.gcd_self⟩

variables {β : Type*} {s : finset β} (f : β → ℕ)

-- this doesn't hold in more generality as most other gcds aren't idempotent, annoyingly
theorem nat_gcd_eq_image : s.gcd f = (s.image f).gcd id := by simp [gcd, fold_image_idem]

theorem mul_dvd {α} [comm_monoid α] {a b c : α} (h : a * b ∣ c) : a ∣ c ∧ b ∣ c :=
begin
  obtain ⟨k, rfl⟩ := h,
  rw mul_assoc,
  nth_rewrite 2 mul_comm,
  rw mul_assoc,
  refine ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩
end

-- Eric: for the love of god I need to come up with a better name
theorem my_dvd_theorem {α} [comm_monoid α] {a b c d : α} (habc : a * b ∣ c) (had : d ∣ a) :
  d * b ∣ c :=
begin
  obtain ⟨k, rfl⟩ := had,
  rw [mul_right_comm] at habc,
  exact (mul_dvd habc).1
end

theorem image_div_gcd_coprime (s : finset ℕ) (h : ¬∀ x ∈ s, x = 0) : s.gcd (/ s.gcd id) = 1 :=
begin
  rw nat.eq_one_iff,
  intros p hp hdvd,
  haveI : fact p.prime := ⟨hp⟩,
  rw dvd_gcd_iff at hdvd,
  replace hdvd : ∀ b ∈ s, s.gcd id * p ∣ b,
  { intros b hb,
    specialize hdvd b hb,
    rwa nat.dvd_div_iff at hdvd,
    apply gcd_dvd hb },

  have : s.gcd id ≠ 0 := (not_iff_not.mpr gcd_eq_zero_iff).mpr h,
  let t := padic_val_nat p (s.gcd id),
  have hpgcd' : ¬ p ^ (t + 1) ∣ s.gcd id := pow_succ_padic_val_nat_not_dvd this.bot_lt,
  replace hdvd : p ^ (t + 1) ∣ s.gcd id,
  { apply dvd_gcd,
    intros b hb,
    rw [pow_succ, mul_comm],
    exact my_dvd_theorem (hdvd b hb) pow_padic_val_nat_dvd },
  contradiction
end

end finset
