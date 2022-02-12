import ring_theory.power_basis
import linear_algebra.matrix.basis

universes u v z

variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S] (B : power_basis R S)

open algebra polynomial

namespace power_basis

def of_mem_adjon {s : S} (hs : B.gen ∈ adjoin R ({s} : set S)) :
  power_basis R S := sorry

lemma of_mem_adjon_gen {s : S} (hs : B.gen ∈ adjoin R ({s} : set S)) :
  (B.of_mem_adjon hs).gen = s := sorry

variables {A : Type z} [comm_ring A] [algebra A R] [algebra A S] {B}

lemma to_matrix_is_integral_coeff {B' : power_basis R S}
  (h : ∃ (P : polynomial A), aeval B.gen P = B'.gen) :
  ∀ i j, _root_.is_integral A (B.basis.to_matrix B'.basis i j) := sorry

end power_basis
