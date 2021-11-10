import data.zmod.basic

-- TODO wow another horrible proof
lemma dvd_of_dvd_zmod {m n a : ℕ} (hmn : m ∣ n) (h : (m : zmod n) ∣ a) : m ∣ a :=
begin
  rcases n with r | n,
  { simp only [int.nat_cast_eq_coe_nat] at h,
    exact_mod_cast h },
  rcases hmn with ⟨k, hk⟩,
  rcases h with ⟨⟨i, hi⟩, hmi⟩,
  rw [(_ : (m : zmod (n + 1)) * ⟨i, hi⟩ = ↑(m * i)), zmod.nat_coe_eq_nat_coe_iff', hk] at hmi,
  cases le_total a (m * i),
  { have := dvd_trans ⟨k, rfl⟩ (nat.dvd_of_mod_eq_zero (nat.sub_mod_eq_zero_of_mod_eq hmi.symm)),
    rw nat.dvd_iff_mod_eq_zero at this,
    zify at this,
    simp only [euclidean_domain.mod_eq_zero] at this,
    simpa only [dvd_neg, sub_sub_cancel_left, int.coe_nat_dvd] using dvd_sub this ⟨↑i, rfl⟩ },
  { have := dvd_trans ⟨k, rfl⟩ (nat.dvd_of_mod_eq_zero (nat.sub_mod_eq_zero_of_mod_eq hmi)),
    apply nat.dvd_of_mod_eq_zero,
    rwa [nat.dvd_iff_mod_eq_zero, nat.sub_mul_mod _ _ _ h] at this },
  { rw [nat.cast_mul],
    congr,
    ext,
    simp [nat.mod_eq_of_lt hi] }
end
