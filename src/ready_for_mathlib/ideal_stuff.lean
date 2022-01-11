import ring_theory.fractional_ideal

universe variables u v w z

variables (n : ℕ+) (K : Type u) (L : Type v) (A : Type w) (B : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

open_locale big_operators non_zero_divisors
open polynomial finset module units fractional_ideal submodule


-- TODO redefine span_singleton as a monoid hom so we get this for free?
@[simp]
lemma fractional_ideal.span_singleton_pow {R : Type*} {P : Type*} [comm_ring R] {S : submonoid R} [comm_ring P]
  [algebra R P] [loc : is_localization S P] (x : P) : ∀ (n : ℕ),
  span_singleton S (x ^ n) = span_singleton S x ^ n
| 0 := by simp
| (n + 1) := by simp [pow_succ, ← fractional_ideal.span_singleton_pow n]

-- TODO this really shouldn't be necessary either?
@[simp]
lemma fractional_ideal.span_singleton_prod {R : Type*} {P ι : Type*} [comm_ring R] {S : submonoid R} [comm_ring P]
  [algebra R P] [loc : is_localization S P] (T : finset ι) (I : ι → P) :
  span_singleton S (∏ t in T, I t) = ∏ t in T, span_singleton S (I t) :=
begin
  classical,
  induction T using finset.induction with i T hiT ih,
  { simp, },
  simp [hiT, span_singleton_mul_span_singleton, ih.symm],
end

@[simp]
lemma ideal.span_singleton_prod {R ι : Type*} [comm_ring R] (T : finset ι) (I : ι → R) :
  ideal.span ({∏ t in T, I t} : set R) = ∏ t in T, ideal.span {I t} :=
begin
  classical,
  induction T using finset.induction with i T hiT ih,
  { simp, },
  simp [hiT, ideal.span_singleton_mul_span_singleton, ih.symm],
end

-- pretty sure there is an easier proof of this
lemma submodule.span_singleton_eq_span_singleton {R : Type*} {M : Type*} [ring R] [add_comm_group M]
  [module R M] [no_zero_smul_divisors R M] (x y : M) :
  span R ({x} : set M) = span R ({y} : set M) ↔ ∃ u : units R, u • x = y :=
begin
  by_cases hyzero : y = 0,
  { simp only [hyzero, span_singleton_eq_bot, span_zero_singleton],
    exact ⟨λ h, by { exact ⟨1, by simp [h]⟩ }, λ ⟨h₁, h₂⟩, by simpa [smul_eq_zero_iff_eq] using h₂⟩ },
  by_cases hxzero : x = 0, { simp [eq_comm, hxzero], },
  have hx : x ∈ span R ({x} : set M) := mem_span_singleton_self _,
  have hy : y ∈ span R ({y} : set M) := mem_span_singleton_self _,
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← h at hy, obtain ⟨v, hv⟩ := submodule.mem_span_singleton.1 hy,
    rw [h] at hx, obtain ⟨w, hw⟩ := submodule.mem_span_singleton.1 hx,
    have hwv : w * v = 1,
    { rw [← one_smul R x, ← hv, ← smul_assoc] at hw,
      simpa using smul_left_injective R hxzero hw },
    have hvw : v * w = 1,
    { rw [← one_smul R y, ← hw, ← smul_assoc] at hv,
      simpa using smul_left_injective R hyzero hv },
    refine ⟨⟨v, w, hvw, hwv⟩, by simpa using hv⟩ },
  { obtain ⟨u, rfl⟩ := h,
    refine le_antisymm (span_le.2 _) (span_le.2 (by simp [submodule.mem_span_singleton_self])),
    rw [set.singleton_subset_iff, set_like.mem_coe, submodule.mem_span_singleton],
    exact ⟨↑u⁻¹, by simp [units.smul_def, ← smul_assoc]⟩ }
end
