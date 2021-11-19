import ring_theory.polynomial.cyclotomic
import number_theory.number_field

open polynomial algebra finite_dimensional module set

universes u v w z

variables (n : ℕ+) (S : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

noncomputable theory

section basic

/-- Given an `A`-algebra `B` and `S : set ℕ+`, we define `is_cyclotomic_extension S A B` requiring
that `cyclotomic a A` has a root in `B` for all `a ∈ S` and that `B` is generated over `A` by the
roots of `X ^ n - 1`. -/
class is_cyclotomic_extension : Prop :=
(ex_root {a : ℕ+} (ha : a ∈ S) : ∃ r : B, aeval r (cyclotomic a A) = 0)
(adjoint_roots : ∀ (x : B), x ∈ adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })

namespace is_cyclotomic_extension

lemma iff : is_cyclotomic_extension S A B ↔
 (∀ (a : ℕ+), a ∈ S → ∃ r : B, aeval r (cyclotomic a A) = 0) ∧
 (∀ x, x ∈ adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) :=
⟨λ h, ⟨h.ex_root, h.adjoint_roots⟩, λ h, ⟨h.1, h.2⟩⟩

lemma iff_adjoin_eq_top : is_cyclotomic_extension S A B ↔
 (∀ (a : ℕ+), a ∈ S → ∃ r : B, aeval r (cyclotomic a A) = 0) ∧
 (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } = ⊤) :=
⟨λ h, ⟨h.ex_root, algebra.eq_top_iff.2 h.adjoint_roots⟩, λ h, ⟨h.1, algebra.eq_top_iff.1 h.2⟩⟩

lemma iff_singleton : is_cyclotomic_extension {n} A B ↔
 (∃ r : B, aeval r (cyclotomic n A) = 0) ∧
 (∀ x, x ∈ adjoin A { b : B | b ^ (n : ℕ) = 1 }) :=
begin
  refine ⟨λ h, ⟨((iff _ _ _).1 h).1 n (set.mem_singleton _), by simpa using ((iff _ _ _).1 h).2⟩,
  λ h, ⟨λ a ha, _, by simpa using h.2⟩⟩,
  obtain ⟨⟨b, hb⟩, H⟩ := h,
  exact ⟨b, (set.mem_singleton_iff.1 ha).symm ▸ hb⟩
end

--is this the best way of stating the result?
lemma empty (h : is_cyclotomic_extension ∅ A B) : (⊤ : subalgebra A B) = ⊥ :=
begin
  replace h := h.adjoint_roots,
  simp only [set.mem_empty_eq, set.set_of_false, adjoin_empty, exists_false, false_and] at h,
  exact (algebra.eq_top_iff.2 h).symm,
end

lemma trans (T : set ℕ+) (C : Type w) [comm_ring C] [algebra A C] [algebra B C]
  [is_scalar_tower A B C] (hS : is_cyclotomic_extension S A B)
  (hT : is_cyclotomic_extension T B C) : is_cyclotomic_extension (S ∪ T) A C :=
begin
  refine ⟨λ n hn, _, λ x, _⟩,
  { cases hn,
    { obtain ⟨b, hb⟩ := ((iff _ _ _).1 hS).1 n hn,
      refine ⟨algebra_map B C b, _⟩,
      replace hb := congr_arg (algebra_map B C) hb,
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ring_hom.map_zero, ← eval₂_at_apply,
        eval₂_eq_eval_map, map_cyclotomic] at hb,
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] },
    { obtain ⟨c, hc⟩ := ((iff _ _ _).1 hT).1 n hn,
      refine ⟨c, _⟩,
      rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hc,
      rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] } },
  { refine adjoin_induction (((iff _ _ _).1 hT).2 x) (λ c ⟨n, hn⟩, subset_adjoin
      ⟨n, or.inr hn.1, hn.2⟩) (λ b, _) (λ x y hx hy, subalgebra.add_mem _ hx hy)
      (λ x y hx hy, subalgebra.mul_mem _ hx hy),
    { let f := is_scalar_tower.to_alg_hom A B C,
      have hb : f b ∈ (adjoin A {b : B | ∃ (a : ℕ+), a ∈ S ∧ b ^ (a : ℕ) = 1}).map f :=
        ⟨b, ((iff _ _ _).1 hS).2 b, rfl⟩,
      rw [is_scalar_tower.to_alg_hom_apply, ← adjoin_image] at hb,
      refine adjoin_mono (λ y hy, _) hb,
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy,
      exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← alg_hom.map_pow, hn.2, alg_hom.map_one]⟩⟩ } }
end

lemma roots_union_eq_union_roots (T : set ℕ+) : {b :B | ∃ (n : ℕ+), n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1} =
  {b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1} ∪
  {b : B | ∃ (n : ℕ+), n ∈ T ∧ b ^ (n : ℕ ) = 1} :=
begin
  refine le_antisymm (λ x hx, _) (λ x hx, _),
  { obtain ⟨n, hn⟩ := hx,
    cases hn.1 with h₁ h₂,
    { left, exact ⟨n, ⟨h₁, hn.2⟩⟩ },
    { right, exact ⟨n, ⟨h₂, hn.2⟩⟩ } },
  { cases hx,
    { obtain ⟨n, hn⟩ := hx,
      exact ⟨n, ⟨or.inl hn.1, hn.2⟩⟩ },
    { obtain ⟨n, hn⟩ := hx,
      exact ⟨n, ⟨or.inr hn.1, hn.2⟩⟩ } }
end

lemma union (T : set ℕ+) (h : is_cyclotomic_extension (S ∪ T) A B)
  : is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B :=
begin
  refine ⟨λ n hn, _, λ b, _⟩,
  { obtain ⟨b, hb⟩ := ((iff _ _ _).1 h).1 n (mem_union_right S hn),
    refine ⟨b, _⟩,
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at hb,
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] },
  { replace h := ((iff _ _ _).1 h).2 b,
    rwa [roots_union_eq_union_roots, adjoin_union_eq_adjoin_adjoin,
      subalgebra.mem_restrict_scalars] at h }
end

end is_cyclotomic_extension

end basic

namespace is_cyclotomic_extension

section fintype

--This is a lemma, but it can be made local instance.
lemma finite [h₁ : fintype S] [h₂ : is_cyclotomic_extension S A B] : finite A B :=
begin
  unfreezingI {revert h₂},
  refine set.finite.dinduction_on (set.finite.intro h₁) (λ h, _) (λ n S hn hS H h, _),
  { refine module.finite_def.2 ⟨({1} : finset B), _⟩,
    simp [← top_to_submodule, empty _ _ h, to_submodule_bot] },
  { sorry }
end

--This is a lemma, but it can be made local instance.
lemma number_field [number_field K] [is_cyclotomic_extension S K L] : number_field L := sorry

--This is a lemma, but it can be made local instance.
lemma finite_dimensional [fintype S] [is_cyclotomic_extension S K L] : finite_dimensional K L :=
finite S K L

end fintype

section field

section singleton

variables [is_cyclotomic_extension {n} K L]

--Add that `X ^ n - 1` splits if `n ∈ S`.
instance splitting_field_X_pow_sub_one : is_splitting_field K L (X ^ (n : ℕ) - 1) := sorry

--Add that `cyclotomic n K` splits if `n ∈ S`.
instance splitting_field_cyclotomic : is_splitting_field K L (cyclotomic n K) := sorry

end singleton

end field

end is_cyclotomic_extension

section cyclotomic_field

/-- Given `n : ℕ+` and a field `K`, we define `cyclotomic n K` as the splitting field of
`cyclotomic n K`. -/
@[derive [field, algebra K, inhabited]]
def cyclotomic_field : Type w := (cyclotomic n K).splitting_field

namespace cyclotomic_field

instance is_cyclotomic_extension : is_cyclotomic_extension {n} K (cyclotomic_field n K) := sorry

end cyclotomic_field

end cyclotomic_field

section is_domain

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

section cyclotomic_ring

/-- If `K` is the fraction field of `A`, the `A`-algebra structure on `cyclotomic_field n K`.
This is not an instance since it causes diamonds when `A = ℤ`. -/
@[nolint unused_arguments]
def cyclotomic_field.algebra_base : algebra A (cyclotomic_field n K) :=
((algebra_map K (cyclotomic_field n K)).comp (algebra_map A K)).to_algebra

local attribute [instance] cyclotomic_field.algebra_base

/-- If `A` is a domain with fraction field `K` and `n : ℕ+`, we define `cyclotomic_ring n A K` as
the `A`-subalgebra of `cyclotomic_field n K` generated by the roots of `X ^ n - 1`. -/
@[derive [comm_ring, inhabited]]
def cyclotomic_ring : Type w := adjoin A { b : (cyclotomic_field n K) | b ^ (n : ℕ) = 1 }

namespace cyclotomic_ring

/-- The `A`-algebra structure on `cyclotomic_ring n A K`.
This is not an instance since it causes diamonds when `A = ℤ`. -/
def algebra_base : algebra A (cyclotomic_ring n A K) := (adjoin A _).algebra

local attribute [instance] cyclotomic_ring.algebra_base

lemma eq_adjoin_single (μ : (cyclotomic_field n K))
  (h : μ ∈ primitive_roots n ((cyclotomic_field n K))) :
  cyclotomic_ring n A K = adjoin A ({μ} : set ((cyclotomic_field n K))) := sorry

instance : is_domain (cyclotomic_ring n A K) := (adjoin A _).is_domain

instance : algebra (cyclotomic_ring n A K) (cyclotomic_field n K) :=
(adjoin A _).to_algebra

instance : is_scalar_tower A (cyclotomic_ring n A K) (cyclotomic_field n K) :=
is_scalar_tower.subalgebra' _ _ _ _

lemma is_cyclotomic_extension : is_cyclotomic_extension {n} A (cyclotomic_ring n A K) := sorry

instance : is_fraction_ring (cyclotomic_ring n A K) (cyclotomic_field n K) := sorry

end cyclotomic_ring

end cyclotomic_ring

end is_domain
