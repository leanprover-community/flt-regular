import number_theory.number_field
import ring_theory.polynomial.cyclotomic
import ring_theory.adjoin_root

open_locale nat real

open polynomial complex

instance polynomial.cyclotomic_rat.irreducible {n : ℕ} (hpos : 0 < n) :
  irreducible (cyclotomic n ℚ) := sorry

def cyclotomic_field (n : ℕ) := adjoin_root (cyclotomic n ℚ)

instance (n : ℕ) : field (cyclotomic_field n) := sorry

def cyclotomic_ring (n : ℕ) := number_field.ring_of_integers (cyclotomic_field n)

theorem cyclotomic_ring_eq_int_adjoin (n : ℕ) : cyclotomic_ring n =
  algebra.adjoin ℤ {adjoin_root.root (cyclotomic n ℚ)} := sorry