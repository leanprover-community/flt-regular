import number_theory.number_field

universe variables u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L]


section pr_11480

-- these 2 were used from when I didn't know `∈ 𝓞 K` was defeq to `is_integral _ ℤ`;
lemma algebra.bot_to_submodule_fg {R A : Type*} [comm_semiring R] [semiring A] [algebra R A] :
  (⊥ : subalgebra R A).to_submodule.fg :=
by { rw algebra.to_submodule_bot, exact ⟨{1}, by simp⟩ }

lemma map_to_submodule {R A B} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
{f : A →ₐ[R] B} (S : subalgebra R A) : (S.map f).to_submodule = S.to_submodule.map f.to_linear_map :=
submodule.ext $ λ x, by simp only [subalgebra.mem_map, exists_prop, alg_hom.to_linear_map_apply,
                                   submodule.mem_map, subalgebra.mem_to_submodule]

end pr_11480

section pr_11476

local notation `𝓞` := number_field.ring_of_integers

instance ring_of_integers_algebra [algebra K L] : algebra (𝓞 K) (𝓞 L) := ring_hom.to_algebra
{ to_fun := λ k, ⟨algebra_map K L k, is_integral.algebra_map k.2⟩,
  map_zero' := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_zero, map_zero],
  map_one'  := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_one, map_one],
  map_add' := λ x y, subtype.ext $ by simp only [map_add, subalgebra.coe_add, subtype.coe_mk],
  map_mul' := λ x y, subtype.ext $ by simp only [subalgebra.coe_mul, map_mul, subtype.coe_mk] }

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 K ↔ is_integral ℤ x := iff.rfl

end pr_11476

-- pr #11474
lemma algebra_map_int_eq : algebra_map ℤ A = int.cast_ring_hom A := rfl
