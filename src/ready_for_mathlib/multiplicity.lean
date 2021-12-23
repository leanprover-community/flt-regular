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

end multiplicity
