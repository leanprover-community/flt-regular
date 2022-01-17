import number_theory.number_field

universe variables u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L]

-- pr #11474
lemma algebra_map_int_eq : algebra_map ℤ A = int.cast_ring_hom A := rfl
