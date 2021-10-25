import number_theory.cyclotomic.field.basic

variables (n : ℕ)  [hn : fact (0 < n)] (R : Type*) (K : Type*)
variables [field K] [char_zero K] [is_cyclotomic_field n K] [comm_ring R] [algebra R K]

open polynomial

section is_cyclotomic_ring

class is_cyclotomic_ring : Prop := (out : is_integral_closure R ℤ K)

namespace is_cyclotomic_ring

instance [is_cyclotomic_ring R K] : is_fraction_ring R K := sorry

instance [h : is_cyclotomic_ring R K] : is_integral_closure R ℤ K := h.out

end is_cyclotomic_ring

end is_cyclotomic_ring

section cyclotomic_ring

include hn
noncomputable
def cyclotomic_ring :=
number_field.ring_of_integers (cyclotomic_field n)

namespace cyclotomic_ring

--generalize this to R using zeta
lemma eq_adjoin : cyclotomic_ring n =
  algebra.adjoin ℤ {adjoin_root.root (cyclotomic n ℚ)} := sorry

end cyclotomic_ring

end cyclotomic_ring
