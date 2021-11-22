import ring_theory.polynomial.cyclotomic
import number_theory.number_field
import algebra.char_p.algebra

open polynomial algebra finite_dimensional module set

universes u v w z

variables (n : ℕ+) (S T : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
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

--Is this the best way of stating the result?
lemma empty [h : is_cyclotomic_extension ∅ A B] : (⊤ : subalgebra A B) = ⊥ :=
begin
  replace h := h.adjoint_roots,
  simp only [set.mem_empty_eq, set.set_of_false, adjoin_empty, exists_false, false_and] at h,
  exact (algebra.eq_top_iff.2 h).symm,
end

--This is a lemma, but it can be made local instance.
lemma trans (C : Type w) [comm_ring C] [algebra A C] [algebra B C]
  [is_scalar_tower A B C] [hS : is_cyclotomic_extension S A B]
  [hT : is_cyclotomic_extension T B C] : is_cyclotomic_extension (S ∪ T) A C :=
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
      have hb : f b ∈ (adjoin A { b : B | ∃ (a : ℕ+), a ∈ S ∧ b ^ (a : ℕ) = 1 }).map f :=
        ⟨b, ((iff _ _ _).1 hS).2 b, rfl⟩,
      rw [is_scalar_tower.to_alg_hom_apply, ← adjoin_image] at hb,
      refine adjoin_mono (λ y hy, _) hb,
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy,
      exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← alg_hom.map_pow, hn.2, alg_hom.map_one]⟩⟩ } }
end

lemma roots_union_eq_union_roots (T : set ℕ+) :
  { b :B | ∃ (n : ℕ+), n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1 } =
  { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 } ∪
  { b : B | ∃ (n : ℕ+), n ∈ T ∧ b ^ (n : ℕ ) = 1 } :=
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

lemma union_right [h : is_cyclotomic_extension (S ∪ T) A B]
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

variables (s: set B)

/-
Do we want to keep this? probably not
lemma adjoin_idem {x : B} (s: set B) : x ∈ adjoin (adjoin A s) s ↔ x ∈ adjoin A s :=
begin
  split,
  { intro hx,
    refine adjoin_induction hx _ _ _ _,
    { intros y hy,
      intros t H, cases H, induction H_h, intros t_1 H, cases H, induction H_h, dsimp at *, simp at *, cases H_w_1, solve_by_elim,},
    { rintro ⟨r, hr⟩,
      assumption, },
    { intros x y,
      exact subalgebra.add_mem _ },
    { intros x y,
      exact subalgebra.mul_mem _ } },
  { intro hx,
    refine adjoin_induction hx _ _ _ _,
    { intros y hy,
    intros t H, cases H, induction H_h, intros t_1 H, cases H, induction H_h, dsimp at *, simp at *, cases H_w_1, solve_by_elim, },
    { intro r,
     let r':=algebra_map A (adjoin A s) r,
      exact subalgebra.algebra_map_mem _ r'},
    { intros x y,
      exact subalgebra.add_mem _ },
    { intros x y,
      exact subalgebra.mul_mem _ } }
end
-/

lemma adjoin_idem' {x : adjoin A s} :
  x ∈ adjoin A {b : adjoin A s | (b : B) ∈ s} ↔ (x : B) ∈ adjoin A s :=
begin
split,
  { intro hx,
    refine adjoin_induction hx _ _ _ _,
    {intros x hxx,
    apply x.property, },
    { intro r,
    simp,
      apply subalgebra.algebra_map_mem _ r, },
    { intros x y,
      exact subalgebra.add_mem _ },
    { intros x y,
      exact subalgebra.mul_mem _ } },
  { intro hx,
   cases x with t ht,
    suffices : ∃ x ∈ adjoin A {b : adjoin A s | (b : B) ∈ s}, ↑x = t,
  {obtain ⟨x, hx, hxx⟩:= this, simp [← hxx, hx],},
    refine adjoin_induction ht (λ b₁ hb₁, _) (λ a, _) (λ b₁ b₂, _) (λ b₁ b₂, _),
    {
      refine ⟨⟨b₁, subset_adjoin hb₁⟩, _⟩,
      simp,
      refine subset_adjoin hb₁,
    },
    { refine ⟨⟨algebra_map A B a, subalgebra.algebra_map_mem _ _⟩, _⟩,
      simp only [exists_prop, set_like.coe_mk, and_true, eq_self_iff_true],
      convert subalgebra.algebra_map_mem _ a,
  },
        { simp only [and_imp, exists_prop, forall_exists_index],
      intros x hxmem hxb y hymem hyb,
      refine ⟨⟨x + y, subalgebra.add_mem _ (by simp) (by simp)⟩, ⟨_, _⟩⟩,
      { simp_rw [← subalgebra.coe_add],
        exact subalgebra.add_mem _ hxmem hymem },
      { simp_rw [hxb, hyb],
        refl } },
    { simp only [and_imp, exists_prop, forall_exists_index],
      intros x hxmem hxb y hymem hyb,
      refine ⟨⟨x * y, subalgebra.mul_mem _ (by simp) (by simp)⟩, ⟨_, _⟩⟩,
      { simp_rw [← subalgebra.coe_mul],
        exact subalgebra.mul_mem _ hxmem hymem },
      { simp_rw [hxb, hyb],
        refl } }
  }
end



lemma union_left [h : is_cyclotomic_extension T A B] (hS : S ⊆ T) :
  is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) :=
begin
  refine ⟨λ n hn, _, λ b, _⟩,
  { obtain ⟨b, hb⟩ := ((iff _ _ _).1 h).1 n (hS hn),
    refine ⟨⟨b, subset_adjoin ⟨n, hn, _⟩⟩, _⟩,
    { rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← is_root.def] at hb,
      suffices : (X ^ (n : ℕ) - 1).is_root b,
      { simpa [sub_eq_zero] using this },
      rw [← (eq_cyclotomic_iff n.pos _).1 rfl],
      exact root_mul_right_of_is_root _ hb },
      rwa [← subalgebra.coe_eq_zero, aeval_subalgebra_coe, subtype.coe_mk] },
  { have:= (adjoin_idem' A B { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }).2 b.property,
   simp at *, norm_cast at this, exact this,

    }
end

end is_cyclotomic_extension

end basic

namespace is_cyclotomic_extension

section fintype

lemma finite_of_singleton [is_domain B] [h : is_cyclotomic_extension {n} A B] : finite A B :=
begin
  classical,
  rw [module.finite_def, ← top_to_submodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2],
  refine fg_adjoin_of_finite _ (λ b hb, _),
  { simp only [mem_singleton_iff, exists_eq_left],
    have : {b : B | b ^ (n : ℕ) = 1} = (nth_roots n (1 : B)).to_finset :=
      set.ext (λ x, ⟨λ h, by simpa using h, λ h, by simpa using h⟩),
    rw [this],
    exact (nth_roots ↑n 1).to_finset.finite_to_set },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hb,
    refine ⟨X ^ (n : ℕ) - 1, ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by simp [hb]⟩⟩ }
end

--This is a lemma, but it can be made local instance.
lemma finite [is_domain B] [h₁ : fintype S] [h₂ : is_cyclotomic_extension S A B] : finite A B :=
begin
  unfreezingI {revert h₂ A B},
  refine set.finite.induction_on (set.finite.intro h₁) (λ A B, _) (λ n S hn hS H A B, _),
  { introsI _ _ _ _ _,
    refine module.finite_def.2 ⟨({1} : finset B), _⟩,
    simp [← top_to_submodule, empty, to_submodule_bot] },
  { introsI _ _ _ _ h,
    haveI : is_cyclotomic_extension S A (adjoin A { b : B | ∃ (n : ℕ+),
      n ∈ S ∧ b ^ (n : ℕ) = 1 }) := union_left _ (insert n S) _ _ (subset_insert n S),
    haveI := H A (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }),
    haveI : finite (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) B,
    { rw [← union_singleton] at h,
      letI := @union_right S {n} A B _ _ _ h,
      exact finite_of_singleton n _ _ },
    exact finite.trans (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) _ }
end

--This is a lemma, but it can be made local instance.
lemma number_field [h : number_field K] [fintype S] [is_cyclotomic_extension S K L] :
  number_field L :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map K L).injective,
  to_finite_dimensional := @finite.trans _ K L _ _ _ _
    (@rat.algebra_rat L _ (char_zero_of_injective_algebra_map (algebra_map K L).injective)) _ _
    h.to_finite_dimensional (finite S K L) }

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
