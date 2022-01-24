import number_theory.cyclotomic.basic
import ring_theory.adjoin.power_basis

import ready_for_mathlib.roots_of_unity

noncomputable theory

open polynomial

universes u v w z

variables (n : ℕ+) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B] [is_cyclotomic_extension {n} A B]

namespace is_cyclotomic_extension

/-- If `B` is a `n`-th cyclotomic extension of `A`, then `zeta n A B` is any root of
`cyclotomic n A` in L. -/
def zeta : B := (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0).some

@[simp] lemma zeta_spec : aeval (zeta n A B) (cyclotomic n A) = 0 :=
classical.some_spec (exists_root (set.mem_singleton n) : ∃ r : B, aeval r (cyclotomic n A) = 0)

lemma zeta_spec' : is_root (cyclotomic n B) (zeta n A B) :=
by { convert zeta_spec n A B, rw [is_root.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic] }

lemma zeta_primitive_root [is_domain B] [ne_zero ((n : ℕ) : B)] :
  is_primitive_root (zeta n A B) n :=
by { rw ←is_root_cyclotomic_iff, exact zeta_spec' n A B }

lemma zeta_pow : (zeta n A B) ^ (n : ℕ) = 1 :=
is_root_of_unity_of (nat.mem_divisors_self _ n.pos.ne') (zeta_spec' _ _ _)

section field

variables (K : Type u) (L : Type v) [field K] [field L] [algebra K L]
variables [is_cyclotomic_extension {n} K L] [ne_zero ((n : ℕ) : K)]

include n

/-- The `power_basis` given by `zeta n K L`. -/
-- this indentation is horrific, and I do not know why term mode doesn't want to work...
@[simps] def zeta.power_basis : power_basis K L :=
begin
haveI : ne_zero ((n : ℕ) : L) := ne_zero.of_no_zero_smul_divisors K L,
refine power_basis.map
  (algebra.adjoin.power_basis $ integral {n} K L $ zeta n K L) _,
exact (subalgebra.equiv_of_eq _ _
      (is_cyclotomic_extension.adjoin_primitive_root_eq_top n _ $ zeta_primitive_root n K L)).trans
      algebra.top_equiv
end

/-- `zeta.embeddings_equiv_primitive_roots` is the equiv between `B →ₐ[A] C` and
  `primitive_roots n C` given by the choice of `zeta`. -/
@[simps]
def zeta.embeddings_equiv_primitive_roots (A K C : Type*) [field A] [field K] [algebra A K]
  [is_cyclotomic_extension {n} A K] [comm_ring C] [is_domain C] [algebra A C]
  [ne_zero ((n : ℕ) : A)] (hirr : irreducible (cyclotomic n A)) :
  (K →ₐ[A] C) ≃ primitive_roots n C :=
have hn : ne_zero ((n : ℕ) : C) := ne_zero.of_no_zero_smul_divisors A C,
have hcyclo : minpoly A (zeta.power_basis n A K).gen = cyclotomic n A :=
(minpoly.eq_of_irreducible_of_monic hirr
  (by rw [zeta.power_basis_gen, zeta_spec]) $ cyclotomic.monic n A).symm,
have h : ∀ x, (aeval x) (minpoly A (zeta.power_basis n A K).gen) = 0 ↔ (cyclotomic n C).is_root x :=
λ x, by rw [aeval_def, eval₂_eq_eval_map, hcyclo, map_cyclotomic, is_root.def],
((zeta.power_basis n A K).lift_equiv).trans
{ to_fun    := λ x, ⟨x.1, by { casesI x, rwa [mem_primitive_roots n.pos, ←is_root_cyclotomic_iff, ←h] }⟩,
  inv_fun   := λ x, ⟨x.1, by { casesI x, rwa [h, is_root_cyclotomic_iff, ←mem_primitive_roots n.pos] }⟩,
  left_inv  := λ x, subtype.ext rfl,
  right_inv := λ x, subtype.ext rfl }

end field

end is_cyclotomic_extension
