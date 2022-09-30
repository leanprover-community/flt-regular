import linear_algebra.basis

variables {R M ι : Type*} [semiring R] [add_comm_monoid M] [module R M]

namespace basis

open_locale big_operators

lemma coord_dvd_of_dvd (b : basis ι R M) (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m) :=
⟨b.coord i m, by simp⟩

lemma coord_repr_symm (b : basis ι R M) (i : ι) (f : ι →₀  R) :
  b.coord i (b.repr.symm f) = f i :=
by simp

lemma coord_equiv_fun_symm [fintype ι] (b : basis ι R M) (i : ι) (f : ι → R) :
  b.coord i (b.equiv_fun.symm f) = f i :=
begin
  classical,
  rw [equiv_fun_symm_apply, linear_map.map_sum],
  conv_lhs { congr, skip, funext,
    rw [linear_map.map_smul, b.coord_apply, b.repr_self_apply] },
  simp
end

end basis
