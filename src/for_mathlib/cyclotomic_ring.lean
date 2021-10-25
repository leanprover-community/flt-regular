import number_theory.number_field
import ring_theory.polynomial.cyclotomic
import ring_theory.adjoin_root

noncomputable theory

open_locale nat real

open polynomial complex

instance polynomial.cyclotomic_rat.irreducible {n : ℕ} [hn : fact (0 < n)] :
  irreducible (cyclotomic n ℚ) :=
by { simpa using ((is_primitive.int.irreducible_iff_irreducible_map_cast
    (monic.is_primitive (cyclotomic.monic n ℤ))).1 (cyclotomic.irreducible hn.out)) }

def cyclotomic_field (n : ℕ) := adjoin_root (cyclotomic n ℚ)

instance (n : ℕ) [fact (0 < n)] : field (cyclotomic_field n) := adjoin_root.field

def cyclotomic_ring (n : ℕ) [fact (0 < n)] :=
number_field.ring_of_integers (cyclotomic_field n)

theorem cyclotomic_ring_eq_int_adjoin (n : ℕ) [fact (0 < n)] : cyclotomic_ring n =
  algebra.adjoin ℤ {adjoin_root.root (cyclotomic n ℚ)} := sorry