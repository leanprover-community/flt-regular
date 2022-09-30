import number_theory.cyclotomic.Unit_lemmas

open_locale number_field

variables {p : ℕ+} {K : Type*} [field K] [char_zero K] [is_cyclotomic_extension {p} ℚ K]
variables {ζ : 𝓞 K} (hζ : is_primitive_root ζ p)

open ideal

variable (i : ℤ)

lemma exists_int_sum_eq_zero (h : p ≠ 2) [hp : fact(p : ℕ).prime] {x y i : ℤ} {u : (𝓞 K)ˣ}
  {α : 𝓞 K} (h : (x : 𝓞 K) + y * ((hζ.is_unit p.pos).unit ^ i : (𝓞 K)ˣ) = u * α ^ (p : ℕ)) :
  ∃ k : ℤ, (x : 𝓞 K) + y * ((hζ.is_unit p.pos).unit ^ i : (𝓞 K)ˣ) -
    ((hζ.is_unit p.pos).unit ^ (2 * k) : (𝓞 K)ˣ) * x -
    ((hζ.is_unit p.pos).unit ^ (2 * k - i) : (𝓞 K)ˣ) * y ∈ span ({p} : set (𝓞 K)) :=
begin
  sorry
end
