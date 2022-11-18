import data.zmod.basic
import algebra.euclidean_domain.instances
import algebra.euclidean_domain.basic

lemma int.dvd_of_dvd_coe_zmod {m a : ℤ} {n : ℕ} (hmn : m ∣ n) (h : (m : zmod n) ∣ a) : m ∣ a :=
begin
  rcases n with r | n,
  { exact_mod_cast h, },
  rcases hmn with ⟨k, hk⟩,
  rcases h with ⟨⟨i, hi⟩, hmi⟩,
  rw [(_ : (m : zmod (n + 1)) * ⟨i, hi⟩ = ↑(m * i)), zmod.int_coe_eq_int_coe_iff', hk] at hmi,
  have : m ∣ a - m * i := dvd_trans ⟨k, rfl⟩ (int.dvd_of_mod_eq_zero
    (int.mod_eq_mod_iff_mod_sub_eq_zero.mp hmi)),
  rw [int.dvd_iff_mod_eq_zero, ← int.dvd_iff_mod_eq_zero] at this,
  exact (dvd_iff_dvd_of_dvd_sub this).mpr (dvd.intro i rfl),
  { rw [int.cast_mul],
    congr,
    simp [nat.mod_eq_of_lt hi], }
end

lemma nat.dvd_of_dvd_coe_zmod {m n a : ℕ} (hmn : m ∣ n) (h : (m : zmod n) ∣ a) : m ∣ a :=
begin
  rcases n with r | n,
  { exact_mod_cast h, },
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
    rwa [nat.dvd_iff_mod_eq_zero, nat.sub_mul_mod _ _ _ h, ← nat.dvd_iff_mod_eq_zero] at this },
  { rw [nat.cast_mul],
    congr,
    simp [nat.mod_eq_of_lt hi], }
end
