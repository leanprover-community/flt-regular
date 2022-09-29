import linear_algebra.basis

variables {R M ι : Type*} [semiring R] [add_comm_monoid M] [module R M]

namespace basis

lemma coord_dvd_of_dvd (b : basis ι R M) (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m) :=
⟨b.coord i m, by simp⟩

end basis
