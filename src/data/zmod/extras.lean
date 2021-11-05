import data.zmod.basic


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
