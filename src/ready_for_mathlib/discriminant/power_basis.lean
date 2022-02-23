import ring_theory.power_basis
import linear_algebra.matrix.basis
import ring_theory.algebraic
import ring_theory.adjoin.power_basis

universes u v z

variables {R : Type z} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S]
variables {K : Type u} {L : Type v} [field K] [field L] [algebra K L] (B : power_basis K L)

open algebra polynomial subalgebra algebra.adjoin

namespace power_basis

lemma adjoin_gen_eq_top (B : power_basis R S) : adjoin R ({B.gen} : set S) = ⊤ :=
begin
  rw [← to_submodule_eq_top, _root_.eq_top_iff, ← B.basis.span_eq, submodule.span_le],
  rintros x ⟨i, rfl⟩,
  rw [B.basis_eq_pow i],
  exact subalgebra.pow_mem _ (subset_adjoin (set.mem_singleton _)) _,
end

lemma adjoin_eq_top_of_gen_mem (B : power_basis R S) {x : S} (hx : B.gen ∈ adjoin R ({x} : set S)) :
  adjoin R ({x} : set S) = ⊤ :=
begin
  rw [_root_.eq_top_iff, ← adjoin_gen_eq_top B],
  refine adjoin_le _,
  simp [hx],
end

/-- The power basis given by `x` if `B.gen ∈ adjoin K {x}`. -/
noncomputable def of_mem_adjon {x : L} (hx : B.gen ∈ adjoin K ({x} : set L)) :
  power_basis K L :=
by { letI := B.finite_dimensional, exact (power_basis $ is_integral_of_finite K L x).map
  ((equiv_of_eq _ _ $ adjoin_eq_top_of_gen_mem B hx).trans top_equiv) }

lemma of_mem_adjon_gen {x : L} (hs : B.gen ∈ adjoin K ({x} : set L)) :
  (B.of_mem_adjon hs).gen = x := rfl

variables [algebra R K] [algebra R L] {B}

lemma to_matrix_is_integral_coeff {B' : power_basis K L}
  (h : ∃ (P : polynomial R), aeval B.gen P = B'.gen) :
  ∀ i j, _root_.is_integral R (B.basis.to_matrix B'.basis i j) := sorry

end power_basis
