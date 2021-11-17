import algebra.gcd_monoid.finset
import ring_theory.int.basic

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

namespace finset

instance : is_idempotent ℕ gcd_monoid.gcd := ⟨nat.gcd_self⟩

variables {β : Type*} {s : finset β} (f : β → ℕ)

-- this doesn't hold in more generality as most other gcds aren't idempotent, annoyingly
theorem nat_gcd_eq_image : s.gcd f = (s.image f).gcd id := by simp [gcd, fold_image_idem]

theorem image_div_gcd_coprime (s : finset ℕ) (h : ¬ s ⊆ {0}) : s.gcd (/ s.gcd id) = 1 :=
begin
  contrapose! h,
  rw [nat.ne_one_iff] at h,
  obtain ⟨p, hp, k, hk⟩ := h,
  rcases k.eq_zero_or_pos with rfl | h,
  { rw [mul_zero, gcd_eq_zero_iff] at hk,
    intros x hx,
    specialize hk x hx,
    apply_fun (* s.gcd id) at hk,
    simp only [zero_mul] at hk,
    rw nat.div_mul_cancel at hk,
    { rw [hk, mem_singleton] },
    exact gcd_dvd hx },
  -- I'm currently in the "come on machine, this is clear nonsense" denial phase
  sorry
end

end finset
