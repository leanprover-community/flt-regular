import algebra.ring.defs
import algebra.group.units

variables {R : Type*} [semiring R]

lemma add_eq_mul_one_add_div {a : Rˣ} {b : R} : ↑a + b = a * (1 + ↑a⁻¹ * b) :=
by rwa [mul_add, mul_one, ← mul_assoc, units.mul_inv, one_mul]
