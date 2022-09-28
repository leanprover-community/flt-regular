import linear_algebra.basis

variables {R M ι : Type*} [semiring R] [add_comm_monoid M] [module R M]

namespace basis

lemma coord_dvd_of_dvd (b : basis ι R M) (i : ι) {m₁ m₂ : M} {r : R} (h : m₂ = r • m₁) :
  r ∣ b.coord i m₂ :=
⟨b.coord i m₁, by simp [h]⟩

end basis
