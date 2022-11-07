import ring_theory.dedekind_domain.ideal
import algebra.big_operators.finsupp

open_locale big_operators

variables {α : Type*} [comm_ring α] [is_domain α] [is_dedekind_domain α]

lemma ideal.is_unit_iff' {R} [comm_semiring R] (I : ideal R) : is_unit I ↔ I = ⊤ :=
begin
  rw [is_unit_iff_dvd_one, ideal.one_eq_top],
  exact ⟨λ h, top_le_iff.mp $ ideal.le_of_dvd h, λ h, h ▸ dvd_rfl⟩,
end

lemma ideal.exists_eq_pow_of_mul_eq_pow (p : nat) {a b c : ideal α} (cp : is_coprime a b)
  (h : a*b = c^p) : ∃ d : ideal α, a = d ^ p :=
begin
  refine exists_eq_pow_of_mul_eq_pow (is_unit_of_dvd_one _ _) h,
  obtain ⟨x, y, hxy⟩ := cp,
  rw [← hxy],
  exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
    (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)
end

open finset

lemma ideal.exists_eq_pow_of_prod_eq_pow {ι : Type*} (p : nat) (c : ideal α)
  {s : finset ι} {f : ι → ideal α} (h : ∀ i j ∈ s, i ≠ j → is_coprime (f i) (f j))
  (hprod : ∏ i in s, f i = c^p) : ∀ i ∈ s, ∃ d : ideal α, f i = d ^ p :=
begin
  classical,
  intros i hi,
  rw [← insert_erase hi, prod_insert (not_mem_erase i s)] at hprod,
  refine ideal.exists_eq_pow_of_mul_eq_pow p
    (is_coprime.prod_right (λ j hj, h i hi j (erase_subset i s hj) (λ hij, _))) hprod,
  rw [hij] at hj,
  exact (s.not_mem_erase _) hj
end
