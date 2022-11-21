import logic.basic

lemma ne_and_eq_iff_right {α : Type*} {a b c : α} (h : b ≠ c) : a ≠ b ∧ a = c ↔ a = c :=
and_iff_right_of_imp (λ h2, h2.symm ▸ h.symm)
