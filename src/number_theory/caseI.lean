import number_theory.gal

open_locale pnat_dangerous

variables (a b c : ℤ) (p : ℕ+) [fact (​p).prime] (h : ¬ ↑p ∣ a * b * c) (hp : 5 ≤ p)

open is_cyclotomic_extension polynomial

local notation `ℤ[ζₚ]` := cyclotomic_ring p ℤ ℚ
local notation `ℚ⟮ζₚ⟯` := cyclotomic_field p ℚ
local notation `ζ` := zeta p ℤ ℤ[ζₚ]
-- this should be a def probably, and with more care about types
local notation `conj` := (aut_equiv_pow ℚ⟮ζₚ⟯ p ℚ $ cyclotomic.irreducible_rat p.pos).symm (-1)

-- we have ℤ+ℚ diamonds everywhere :)
local attribute [instance] cyclotomic_ring.algebra_base

--set_option trace.class_instances true

lemma case_one : a ^ ​p + b ^ ​p ≠ c ^ ​p :=
begin
  haveI : is_dedekind_domain ℤ[ζₚ] := sorry, -- Riccardo says this is very close
  have units_lemma : ∀ x : ℤ[ζₚ]ˣ, ∃ u : ℤ[ζₚ]ˣ, ∃ n : ℕ, ↑x = ζ ^ n * u,
  { have norm_lemma : ∀ x : ℚ⟮ζₚ⟯, algebra.norm ℚ x = 1 → x ^ ​p = 1,
    { /- This holds in more generality for all extensions, but you must have that the norm of all
      conjugates is one. This is not relevant here, as this follows from the abelian Galois group -
      it is a `noncomputable example` in `gal.lean`. -/
      sorry },
    intro x,
    --let α := x / conj x,
    sorry },
  sorry
end
