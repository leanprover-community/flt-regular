import ring_theory.multiplicity

variables {α : Type*}

namespace multiplicity

variables [comm_monoid α] [decidable_rel ((∣) : α → α → Prop)]

open nat

lemma pos_of_dvd {a b : α} (hfin : finite a b) (hdiv : a ∣ b) : 0 < (multiplicity a b).get hfin :=
begin
  refine zero_lt_iff.2 (λ h, _),
  simpa [hdiv] using (is_greatest' hfin (lt_one_iff.mpr h)),
end

lemma eq_pow_mul_not_dvd {a b : α} (hfin : finite a b) :
  ∃ (c : α), b = a ^ ((multiplicity a b).get hfin) * c ∧ ¬ a ∣ c :=
begin
  obtain ⟨c, hc⟩ := multiplicity.pow_multiplicity_dvd hfin,
  refine ⟨c, hc, _⟩,
  rintro ⟨k, hk⟩,
  rw [hk, ← mul_assoc, ← pow_succ'] at hc,
  have h₁ : a ^ ((multiplicity a b).get hfin + 1) ∣ b := ⟨k, hc⟩,
  exact (multiplicity.eq_coe_iff.1 (by simp)).2 h₁,
end

end multiplicity
