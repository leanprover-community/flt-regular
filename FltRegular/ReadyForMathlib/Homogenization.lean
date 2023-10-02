/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best

! This file was ported from Lean 3 source module ready_for_mathlib.homogenization
-/
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.Set.Finite
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.SymmDiff

/-!
# Homogenization

## Main definitions

* `mv_polynomial.homogenization`

## Main statements

* foo_bar_unique

## Notation



## Implementation details

* We homogenize polynomials over a given ground set of variables, rather than adjoining an extra
  variable to give the user more choice in the type of the polynomials involved.

## References

* [F. Bar, *Quuxes*][]

## Tags


-/


variable {R ι : Type _} [CommSemiring R]

open Polynomial Finset MvPolynomial

open scoped BigOperators

noncomputable section

namespace MvPolynomial

section Finsupp

-- TODO can any assumptions be weakened
-- TODO version with monoid hom?
theorem Finsupp.sum_update_add {α β : Type _} [AddCommMonoid α] [AddCommMonoid β] (f : ι →₀ α)
    (i : ι) (a : α) (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
    (hgg : ∀ (a : ι) (b₁ b₂ : α), g a (b₁ + b₂) = g a b₁ + g a b₂) :
    (f.update i a).sum g + g i (f i) = f.sum g + g i a := by
  classical
  simp_rw [Finsupp.update_eq_erase_add_single]
  rw [Finsupp.sum_add_index (fun i _ => hg i) fun i _ => hgg i]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [Finsupp.update_eq_erase_add_single]
  rw [Finsupp.sum_add_index (fun i _ => hg i) fun i _ => hgg i]
  rw [add_assoc]
  rw [add_assoc]
  congr 1
  rw [add_comm]
  rw [Finsupp.sum_single_index (hg _)]
  rw [Finsupp.sum_single_index (hg _)]

end Finsupp

/-- The homogenization of a multivariate polynomial at a single variable. -/
def homogenization (i : ι) (p : MvPolynomial ι R) : MvPolynomial ι R :=
  -- ∑ j in p.support, monomial (j + finsupp.single i (p.total_degree - (j i))) (p.coeff j)
    Finsupp.mapDomain
    (fun j => j + Finsupp.single i (p.totalDegree - j.sum fun _ m => m)) p

namespace Finsupp

open Finsupp

@[simp]
theorem support_mapDomain {α β M : Type _} [AddCommMonoid M] (f : α ↪ β) (v : α →₀ M) :
    (Finsupp.mapDomain f v).support ⊆ v.support.map f := by
  classical
  rw [Finsupp.mapDomain]
  refine' Finset.Subset.trans Finsupp.support_sum _
  simp only [Finsupp.mem_support_iff, Finset.biUnion_subset_iff_forall_subset, Ne.def]
  intro x hx
  apply Finset.Subset.trans Finsupp.support_single_subset
  simp [hx]

theorem mapDomain_apply' {α β M : Type _} [AddCommMonoid M] (S : Set α) {f : α → β} (x : α →₀ M)
    (hS : (x.support : Set α) ⊆ S) (hf : Set.InjOn f S) {a : α} (ha : a ∈ S) :
    Finsupp.mapDomain f x (f a) = x a := by
  classical
  rw [Finsupp.mapDomain]
  simp only [Finsupp.sum_apply]
  rw [Finsupp.sum]
  simp_rw [Finsupp.single_apply]
  have : ∀ (a_1 : α) (_ : a_1 ∈ x.support),
      (if f a_1 = f a then x a_1 else 0) = if f a_1 = f a then x a else 0 := by
    intro a_1 ha_1
    split_ifs with hh
    rw [hf _ ha hh]
    exact hS ha_1
    rfl
  by_cases ha : a ∈ x.support
  · rw [← Finset.add_sum_erase _ _ ha]
    simp only [if_true, eq_self_iff_true]
    convert add_zero (x a)
    have h : ∀ i ∈ x.support.erase a, f i ≠ f a := by
      intro i hi
      have hix : i ∈ x.support := Finset.mem_of_mem_erase hi
      have hia : i ≠ a := Finset.ne_of_mem_erase hi
      exact hia ∘ hf (hS hix) (hS ha)
    rw [← Finset.sum_coe_sort]
    conv_lhs =>
      congr; rfl; ext i
      rw [if_neg (h i.1 i.2)]
    simp only [Finset.sum_const_zero]
  · simp at ha
    rw [← Finset.sum_coe_sort]
    conv_lhs =>
      congr; rfl; ext i
      rw [this i.1 i.2]
    simp [ha]

theorem mapDomain_injOn {α β M : Type _} [AddCommMonoid M] (S : Set α) {f : α → β}
    (hf : Set.InjOn f S) :
    Set.InjOn (Finsupp.mapDomain f : (α →₀ M) → β →₀ M) {w | (w.support : Set α) ⊆ S} :=
  by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  have : Finsupp.mapDomain f v₁ (f a) = Finsupp.mapDomain f v₂ (f a) := by rw [eq]
  rw [Set.mem_setOf_eq] at hv₁ hv₂
  classical
  have hu : (v₁.support ∪ v₂.support : Set α) ⊆ S := Set.union_subset hv₁ hv₂
  by_cases h : a ∈ v₁.support ∪ v₂.support
  · rwa [mapDomain_apply' S _ hv₁ hf _, mapDomain_apply' S _ hv₂ hf _] at this
    · apply hu
      exact_mod_cast h
    · apply hu
      exact_mod_cast h
  · simp only [not_or, mem_union, Classical.not_not, Finsupp.mem_support_iff] at h
    simp [h]

-- rw [finsupp.map_domain_apply hf, finsupp.map_domain_apply hf] at this,
end Finsupp

-- lemma support_homogenization [decidable_eq ι] (i : ι) (p : mv_polynomial ι R)
--   (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : (p.homogenization i).support = p.support.image
--     (λ (j : ι →₀ ℕ), j + finsupp.single i (p.total_degree - j.sum (λ (_x : ι) (m : ℕ), m))) :=
-- begin
--   rw homogenization,
--   apply finsupp.support_map_domain _ _ _,
-- end
@[simp]
theorem homogenization_zero (i : ι) : (0 : MvPolynomial ι R).homogenization i = 0 := by
  simp [homogenization]

-- TODO this is probably useless
-- lemma map_domain_one {α β M : Type*} [has_zero β] [has_zero α] [has_one M]
--   [add_comm_monoid M] {f : α → β} (hf : f 0 = 0) :
--   finsupp.map_domain f (finsupp.single 0 1 : α →₀ M) = (finsupp.single 0 1 : β →₀ M) :=
-- by simp [hf]
-- TODO maybe instead prove this via is_homogeneous_one
@[simp]
theorem homogenization_one (i : ι) : (1 : MvPolynomial ι R).homogenization i = 1 :=
  by
  simp only [homogenization, totalDegree_one, zero_tsub, add_zero, Finsupp.single_zero]
  erw [Finsupp.mapDomain_single]
  -- erw map_domain_one,
  rfl

@[simp]
theorem homogenization_C (i : ι) (c : R) : (C c : MvPolynomial ι R).homogenization i = C c :=
  by
  simp only [homogenization, totalDegree_C, zero_tsub]
  convert Finsupp.mapDomain_single (M := R) using 1
  rw [single_eq_monomial]
  have : (0 : ι →₀ ℕ) i = 0 := by simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [← this]
  simp

@[simp]
theorem homogenization_monomial (i : ι) (s : ι →₀ ℕ) (r : R) :
    (monomial s r : MvPolynomial ι R).homogenization i = monomial s r := by
  by_cases hr : r = 0
  · simp [hr]
  erw [homogenization, Finsupp.mapDomain_single, single_eq_monomial, totalDegree_monomial _ hr,
    tsub_self]
  simp

-- TODO name this
theorem aux {i : ι} {p : MvPolynomial ι R} {x : ι →₀ ℕ} (hp : x ∈ p.support) :
    ((x + Finsupp.single i (p.totalDegree - x.sum fun _ m => m)).sum fun _ m => m) =
      p.totalDegree := by
  classical
  rw [Finsupp.sum_add_index]
  rw [Finsupp.sum_single_index]
  rw [add_tsub_cancel_iff_le]
  apply Finset.le_sup hp
  rfl
  intros
  rfl
  intros
  rfl

theorem isHomogeneous_homogenization (i : ι) (p : MvPolynomial ι R) :
    (p.homogenization i).IsHomogeneous p.totalDegree := by
  letI := Classical.decEq ι
  rw [homogenization]
  intro d hd
  rw [Finsupp.mapDomain, Finsupp.sum, coeff_sum] at hd
  simp_rw [single_eq_monomial, coeff_monomial] at hd
  contrapose! hd
  have : ∀ (x : ι →₀ ℕ) (_ : x ∈ p.support),
      ¬x + Finsupp.single i (p.totalDegree - x.sum fun (_x : ι) (m : ℕ) => m) = d := by
    intro x hx hh
    apply hd
    rw [← hh]
    change ((x + Finsupp.single i (p.totalDegree - x.sum fun _ m => m)).sum fun _ m => m) = _
    rw [aux hx]
  rw [← Finset.sum_coe_sort]
  conv_lhs =>
    congr; rfl; ext i
    rw [if_neg (this i.1 i.2)]
  simp

theorem homogenization_of_isHomogeneous (n : ℕ) (i : ι) (p : MvPolynomial ι R)
    (hp : p.IsHomogeneous n) : p.homogenization i = p := by
  by_cases hpn : p = 0
  · simp [hpn]
  rw [homogenization]
  have := (hp.totalDegree hpn).symm
  subst this
  rw [IsHomogeneous] at hp
  have : ∀ (x) (_ : x ∈ p.support),
      (fun j : ι →₀ ℕ => j + Finsupp.single i (p.totalDegree - j.sum fun (_x : ι) (m : ℕ) => m))
          x = x := by
    intro x hx
    simp only [add_right_eq_self, Finsupp.single_eq_same, tsub_eq_zero_iff_le, Finsupp.single_tsub,
      Finsupp.single_le_iff]
    rw [← hp (mem_support_iff.mp hx)]
    exact le_refl _
  rw [Finsupp.mapDomain_congr this]
  -- simp,
  erw [Finsupp.mapDomain_id]

-- TODO there should be a simp lemma version of this for λ x, x so simp works
theorem homogenization_idempotent (i : ι) (p : MvPolynomial ι R) :
    (p.homogenization i).homogenization i = p.homogenization i := by
  classical
  apply homogenization_of_isHomogeneous p.totalDegree
  exact isHomogeneous_homogenization _ _

-- TODO should these hjp assumptions be phrased using `degree_of` or `vars`?
theorem homogenization_ne_zero_of_ne_zero (i : ι) {p : MvPolynomial ι R} (hp : p ≠ 0)
    (hjp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : p.homogenization i ≠ 0 := by
  intro h
  apply hp
  have :
    Set.InjOn (fun j : ι →₀ ℕ => j + Finsupp.single i (p.totalDegree - j.sum fun _ m => m))
      {w | w i = 0} :=
    by
    intro t ht y hy hh
    simp only [Set.mem_setOf_eq] at hh hy ht
    ext a
    have :
      (t + Finsupp.single i (p.totalDegree - t.sum fun _ m => m)) a =
        (y + Finsupp.single i (p.totalDegree - y.sum fun _ m => m)) a :=
      by rw [hh]
    simp only [Finsupp.coe_add, Pi.add_apply] at this
    classical
    rw [Finsupp.single_apply, Finsupp.single_apply] at this
    split_ifs at this  with hia
    · rw [← hia, ht, hy]
    · simpa
  refine' Finsupp.mapDomain_injOn _ this _ _ h
  · intro x hx
    rw [Set.mem_setOf_eq, hjp x hx]
  · simp only [Set.mem_setOf_eq]
    intro x hx
    simp only [mem_coe, Finsupp.mem_support_iff, ne_eq] at hx
    change ¬ 0 = 0 at hx
    simp only [not_true] at hx

-- refine finsupp.map_domain_injective _ h,
-- intros x y hxy,
-- simp at hxy,
-- -- TODO something like this but this isnt exactly true
-- admit,
-- TODO this can follow from previous
theorem totalDegree_homogenization (i : ι) (p : MvPolynomial ι R)
    (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
    (p.homogenization i).totalDegree = p.totalDegree := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  apply IsHomogeneous.totalDegree
  refine' isHomogeneous_homogenization _ _
  exact homogenization_ne_zero_of_ne_zero _ hp h

-- rw total_degree,
-- have : (homogenization i p).support.nonempty,
-- { simp [homogenization],
--   admit,
--    },
-- rw ← finset.sup'_eq_sup this,
-- rw finset.nonempty.sup'_eq_cSup_image,
-- suffices : (λ (s : ι →₀ ℕ), s.sum (λ (n : ι) (e : ℕ), e)) '' ↑((homogenization i p).support) =
--   {p.total_degree},
-- { simp [this], },
-- refine set.eq_singleton_iff_unique_mem.mpr _,
-- split,
-- { simp, admit, },
-- { simp, admit, },
section LeadingTerms

-- TODO is this the best def?
/-- The sum of the monomials of highest degree of a multivariate polynomial. -/
def leadingTerms (p : MvPolynomial ι R) : MvPolynomial ι R :=
  homogeneousComponent p.totalDegree p

theorem leadingTerms_apply (p : MvPolynomial ι R) :
    p.leadingTerms =
      ∑ d in p.support.filter fun d => ∑ i in d.support, d i = p.totalDegree,
        monomial d (coeff d p) :=
  homogeneousComponent_apply _ _

-- (p.support.filter (λ s : ι →₀ ℕ, s.sum (λ _ e, e) = p.total_degree)).sum $
--   λ s, monomial s (p.coeff s)
-- TODO for non-zero polys this is true that p.lead = p iff p.is_homogenous n for a fixed n
-- TODO generalize to p.homog comp = n
theorem leadingTerms_eq_self_iff_isHomogeneous (p : MvPolynomial ι R) :
    p.leadingTerms = p ↔ p.IsHomogeneous p.totalDegree := by
  constructor <;> intro h
  · rw [IsHomogeneous]
    contrapose! h
    rcases h with ⟨h_w, h_h₁, h_h₂⟩
    rw [leadingTerms, Ne.def, MvPolynomial.ext_iff]
    push_neg
    use h_w
    classical
    change ¬(h_w.sum fun (_x : ι) (e : ℕ) => e) = p.totalDegree at h_h₂
    simp only [h_h₁.symm, coeff_homogeneousComponent, exists_prop, and_true_iff, Ne.def,
      not_false_iff, not_forall, ite_eq_left_iff]
    convert h_h₂
  · rw [leadingTerms_apply]
    rw [(_ :
        (p.support.filter fun s : ι →₀ ℕ => ∑ i : ι in s.support, s i = p.totalDegree) =
          p.support)]
    · rw [support_sum_monomial_coeff p]
    · rw [Finset.filter_eq_self]
      intro s hs
      rw [mem_support_iff] at hs
      rw [← h hs]

@[simp]
theorem leadingTerms_C (r : R) : (C r : MvPolynomial ι R).leadingTerms = C r := by
  rw [leadingTerms_eq_self_iff_isHomogeneous]
  convert isHomogeneous_C (R := R) _ _
  simp

@[simp]
theorem leadingTerms_zero : (0 : MvPolynomial ι R).leadingTerms = 0 := by simp [leadingTerms]

@[simp]
theorem leadingTerms_one : (1 : MvPolynomial ι R).leadingTerms = 1 := by simp [leadingTerms]

@[simp]
theorem leadingTerms_monomial (s : ι →₀ ℕ) (r : R) :
    (monomial s r).leadingTerms = monomial s r := by
  by_cases hr : r = 0
  · simp [hr]
  rw [leadingTerms_eq_self_iff_isHomogeneous]
  convert isHomogeneous_monomial (R := R) _ _ _ _
  simp [totalDegree_monomial _ hr]
  rfl

section DangerousInstance

attribute [local instance] MvPolynomial.unique

@[simp]
theorem leadingTerms_X (s : ι) : (X s : MvPolynomial ι R).leadingTerms = X s := by
  nontriviality R
  rw [leadingTerms_eq_self_iff_isHomogeneous]
  convert isHomogeneous_X _ _
  exact totalDegree_X _

end DangerousInstance

theorem isHomogeneous_leadingTerms (p : MvPolynomial ι R) :
    p.leadingTerms.IsHomogeneous p.totalDegree :=
  homogeneousComponent_isHomogeneous (totalDegree p) p

theorem exists_coeff_ne_zero_totalDegree {p : MvPolynomial ι R} (hp : p ≠ 0) :
    ∃ v : ι →₀ ℕ, (v.sum fun _ e => e) = p.totalDegree ∧ p.coeff v ≠ 0 := by
  obtain ⟨b, hb₁, hb₂⟩ :=
    p.support.exists_mem_eq_sup (Finsupp.support_nonempty_iff.mpr hp) fun m : ι →₀ ℕ =>
      Multiset.card (Finsupp.toMultiset m)
  use b
  constructor
  · rw [← totalDegree_eq p] at hb₂
    rw [hb₂]
    dsimp

    -- TODO break this out as a lemma
    exact (Finsupp.card_toMultiset _).symm
  · exact mem_support_iff.mp hb₁

theorem support_add_eq [DecidableEq ι] {g₁ g₂ : MvPolynomial ι R}
    (h : Disjoint g₁.support g₂.support) : (g₁ + g₂).support = g₁.support ∪ g₂.support :=
  Finsupp.support_add_eq h

theorem add_ne_zero_of_ne_zero_of_support_disjoint (p q : MvPolynomial ι R) (hp : p ≠ 0)
    (h : Disjoint p.support q.support) : p + q ≠ 0 := by
  classical
  contrapose! hp
  have := congr_arg support hp
  rw [support_zero, support_add_eq h,
    Finset.union_eq_empty,-- TODO should this be simp?
    MvPolynomial.support_eq_empty] at this
  exact this.left

theorem support_sum_monomial_eq [DecidableEq R] (S : Finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
    support (∑ v in S, monomial v (f v)) = S.filter fun v => f v ≠ 0 :=
  by
  letI := Classical.decEq ι
  induction' S using Finset.induction with s S hs hsi
  · simp
  rw [Finset.sum_insert hs, support_add_eq]
  · rw [hsi, filter_insert, support_monomial]
    split_ifs with h h' <;> simp [h, insert_eq]; exact h' h
  · apply disjoint_of_subset_left support_monomial_subset
    simp [hsi, hs]

theorem support_sum_monomial_subset (S : Finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
    support (∑ v in S, monomial v (f v)) ⊆ S := by
  classical
  rw [support_sum_monomial_eq]
  apply filter_subset

theorem sum_monomial_ne_zero_of_exists_mem_ne_zero (S : Finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R)
    (h : ∃ (s : _) (_ : s ∈ S), f s ≠ 0) : ∑ s : ι →₀ ℕ in S, monomial s (f s) ≠ 0 := by
  classical
  simp only [← support_eq_empty, support_sum_monomial_eq, Ne.def]
  rcases h with ⟨s, h_S, h_s⟩
  exact ne_empty_of_mem (mem_filter.mpr ⟨h_S, h_s⟩)

theorem leadingTerms_ne_zero {p : MvPolynomial ι R} (hp : p ≠ 0) : p.leadingTerms ≠ 0 := by
  classical
  rw [leadingTerms_apply]
  apply sum_monomial_ne_zero_of_exists_mem_ne_zero
  simp only [exists_prop, mem_support_iff, Finset.mem_filter]
  obtain ⟨f, hf, hf0⟩ := exists_coeff_ne_zero_totalDegree hp
  exact ⟨f, ⟨hf0, hf⟩,  hf0⟩

@[simp]
theorem totalDegree_homogenous_component_of_ne_zero {n : ℕ} {p : MvPolynomial ι R}
    (hp : homogeneousComponent n p ≠ 0) : (homogeneousComponent n p).totalDegree = n :=
  IsHomogeneous.totalDegree (homogeneousComponent_isHomogeneous n p) hp

@[simp]
theorem totalDegree_leadingTerms (p : MvPolynomial ι R) :
    p.leadingTerms.totalDegree = p.totalDegree :=
  by
  by_cases hp : p = 0
  · simp [hp]
  exact totalDegree_homogenous_component_of_ne_zero (leadingTerms_ne_zero hp)

-- TODO generalize this to homogeneous component idempotent?
theorem leadingTerms_idempotent (p : MvPolynomial ι R) :
    p.leadingTerms.leadingTerms = p.leadingTerms :=
  by
  rw [leadingTerms_eq_self_iff_isHomogeneous, totalDegree_leadingTerms]
  exact isHomogeneous_leadingTerms p

-- TODO lol this isn't true
-- lemma homogeneous_component_mul (m n : ℕ) (p q : mv_polynomial ι R) :
--   homogeneous_component (m + n) (p * q) = homogeneous_component m p * homogeneous_component n q :=
-- begin
--   admit,
-- end
theorem coeff_leadingTerms (p : MvPolynomial ι R) (d : ι →₀ ℕ) :
    coeff d p.leadingTerms = if ∑ i in d.support, d i = p.totalDegree then coeff d p else 0 :=
  coeff_homogeneousComponent _ _ _

theorem support_homogeneousComponent (n : ℕ) (p : MvPolynomial ι R) :
    (homogeneousComponent n p).support = p.support.filter fun d => (d.sum fun _ m => m) = n :=
  by
  rw [homogeneousComponent]
  simp only [Finsupp.restrictDom_apply, Submodule.subtype_apply, Function.comp_apply,
    LinearMap.coe_comp, Set.mem_setOf_eq]
  erw [← Finsupp.support_filter]
  rfl

theorem support_homogeneousComponent_subset (n : ℕ) (p : MvPolynomial ι R) :
    (homogeneousComponent n p).support ⊆ p.support :=
  by
  rw [support_homogeneousComponent]
  exact Finset.filter_subset _ _

theorem support_leadingTerms (p : MvPolynomial ι R) :
    p.leadingTerms.support = p.support.filter fun d => (d.sum fun _ m => m) = p.totalDegree :=
  support_homogeneousComponent _ _

theorem support_leadingTerms_subset (p : MvPolynomial ι R) : p.leadingTerms.support ⊆ p.support :=
  support_homogeneousComponent_subset _ _

theorem eq_leadingTerms_add (p : MvPolynomial ι R) (hp : p.totalDegree ≠ 0) :
    ∃ p_rest : MvPolynomial ι R, p = p.leadingTerms + p_rest ∧
    p_rest.totalDegree < p.totalDegree := by
  letI := Classical.decEq ι
  exists ∑ v : ι →₀ ℕ in p.support \ p.leadingTerms.support, (monomial v) (coeff v p)
  constructor
  · nth_rw 1 [p.leadingTerms.as_sum]
    have : ∀ (x : ι →₀ ℕ) (_ : x ∈ p.leadingTerms.support), x.support.sum x = p.totalDegree :=
      by
      intro x hx
      rw [support_leadingTerms] at hx
      simp at hx
      exact hx.2
    simp_rw [coeff_leadingTerms]
    rw [← Finset.sum_coe_sort (support (leadingTerms p))]
    conv_rhs =>
      congr; congr; rfl; ext i;
      rw [this i.1 i.2]
    simp only [ite_true]
    rw [Finset.sum_coe_sort _ (fun x => (monomial x) (coeff x p))]
    have : p.leadingTerms.support ⊆ p.support := support_leadingTerms_subset _
    have : p.leadingTerms.support ∩ p.support = p.leadingTerms.support := by
      rw [Finset.inter_eq_left]
      exact this
    nth_rw 1 [← this]
    rw [Finset.inter_comm, Finset.sum_inter_add_sum_diff]
    exact p.as_sum
  · rw [totalDegree, Finset.sup_lt_iff]
    intro b hb
    rw [support_leadingTerms] at hb
    rw [← Finset.filter_not] at hb
    -- TODO this was also hard to find maybe a negated version is good
    have := support_sum_monomial_subset _ _ hb
    simp only [Finset.mem_filter] at this
    cases' this with this_left this_right
    rw [totalDegree]
    refine' lt_of_le_of_ne (by apply Finset.le_sup this_left) this_right
    rw [bot_eq_zero]
    exact pos_iff_ne_zero.mpr hp

theorem leadingTerms_add_of_totalDegree_lt (p q : MvPolynomial ι R)
    (h : q.totalDegree < p.totalDegree) : (p + q).leadingTerms = p.leadingTerms := by
  rw [leadingTerms, leadingTerms, totalDegree_add_eq_left_of_totalDegree_lt h,
    LinearMap.map_add, homogeneousComponent_eq_zero _ q h, add_zero]

-- lemma C_mul_eq_smul {r : R} (p : mv_polynomial ι R) : C r * p = r • p :=
-- by rw [C_eq_smul_one, algebra.smul_mul_assoc, one_mul]
theorem NoZeroSmulDivisors.smul_eq_zero_iff_eq_zero_or_eq_zero (R M : Type _) [Zero R] [Zero M]
    [SMulWithZero R M] [NoZeroSMulDivisors R M] {c : R} {x : M} : c • x = 0 ↔ c = 0 ∨ x = 0 := by
  constructor <;> intro h
  exact eq_zero_or_eq_zero_of_smul_eq_zero h
  cases' h with h h <;> simp [h]

--TODO this generalized lemma when distrib_mul_action_with_zero exists?
-- lemma support_smul_eq {α M R : Type*} {_ : monoid_with_zero R} [add_monoid M]
--   [distrib_mul_action_with_zero R M] [no_zero_smul_divisors R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} :
--   (b • g).support = g.support :=
-- begin
--   ext a,
--   simp [finsupp.smul_apply, mem_support_iff, ne.def],
--   simp,
--   rw no_zero_smul_divisors.smul_eq_zero_iff_eq_zero_or_eq_zero,
-- end
-- haveI : no_zero_smul_divisors R (mv_polynomial ι R), --TODO add this instance
--TODO maybe this for leading terms and homog
-- lemma homogeneous_s_monomial_mul [no_zero_divisors R] (p : mv_polynomial ι R) (r : R) (x : ι →₀ ℕ) :
-- (p * monomial x r).leading_terms = p.leading_terms * monomial x r :=
--TODO also maybe an smul version
@[simp]
theorem leadingTerms_C_mul [NoZeroSMulDivisors R R] (p : MvPolynomial ι R) (r : R) :
    leadingTerms (C r * p) = C r * p.leadingTerms := by
  by_cases hr : r = 0
  · simp [hr]
  have : support (C r * p) = p.support := by
    rw [C_mul']
    exact Finsupp.support_smul_eq hr
  rw [leadingTerms, leadingTerms, totalDegree, this, homogeneousComponent_C_mul]
  rfl

theorem eq_C_of_totalDegree_zero {p : MvPolynomial ι R} (hp : p.totalDegree = 0) :
    p = C (coeff 0 p) := by
  letI := Classical.decEq ι
  erw [Finset.sup_eq_bot_iff] at hp
  simp only [mem_support_iff] at hp
  ext m
  by_cases hm : m = 0
  · simp [hm]
  rw [coeff_C, if_neg (Ne.symm hm)]
  classical
  by_contra h
  specialize hp m h
  apply hm
  rw [Finsupp.sum] at hp
  -- TODO this and line below could be a lemma, finsupp.sum_eq_zero_iff?
  simp only [not_imp_self, bot_eq_zero, Finsupp.mem_support_iff, Finset.sum_eq_zero_iff] at hp
  ext
  simp [hp]

-- TODO can things be generalized to no_zero_divisors (would require an instance for mv_poly)
-- sadly this adds some imports and requirements not needed in rest of file
@[simp]
theorem leadingTerms_mul {S : Type _} [CommRing S] [IsDomain S] (p q : MvPolynomial ι S) :
    (p * q).leadingTerms = p.leadingTerms * q.leadingTerms := by
  by_cases hp : p.totalDegree = 0
  · rw [eq_C_of_totalDegree_zero hp, leadingTerms_C_mul, leadingTerms_C]
  by_cases hq : q.totalDegree = 0
  · rw [eq_C_of_totalDegree_zero hq, mul_comm, leadingTerms_C_mul, leadingTerms_C, mul_comm]
  have : (p.leadingTerms * q.leadingTerms).totalDegree = p.totalDegree + q.totalDegree :=
    by
    rw [IsHomogeneous.totalDegree]
    apply IsHomogeneous.mul (isHomogeneous_leadingTerms p) (isHomogeneous_leadingTerms q)
    apply mul_ne_zero
    · apply leadingTerms_ne_zero
      rintro rfl
      exact hp totalDegree_zero
    · apply leadingTerms_ne_zero
      rintro rfl
      exact hq totalDegree_zero
  rcases eq_leadingTerms_add p hp with ⟨wp, hp, tp⟩
  rcases eq_leadingTerms_add q hq with ⟨wq, hq, tq⟩
  rw [hp, hq]
  simp only [add_mul, mul_add]
  rw [add_assoc, leadingTerms_add_of_totalDegree_lt, leadingTerms_add_of_totalDegree_lt,
    leadingTerms_add_of_totalDegree_lt, leadingTerms_idempotent, leadingTerms_idempotent,
    leadingTerms_eq_self_iff_isHomogeneous]
  · rw [this]
    exact IsHomogeneous.mul (isHomogeneous_leadingTerms p) (isHomogeneous_leadingTerms q)
  · rwa [totalDegree_leadingTerms]
  · rwa [totalDegree_leadingTerms]
  · rw [this]
    calc
      _ ≤ max (wp * (leadingTerms q)).totalDegree ((leadingTerms p) * wq + wp * wq).totalDegree :=
        totalDegree_add _ _
      _ ≤
          max (wp * (leadingTerms q)).totalDegree
            (max ((leadingTerms p) * wq).totalDegree (wp * wq).totalDegree) :=
        (max_le_max (le_refl _) (totalDegree_add _ _))
      _ ≤
          max (wp.totalDegree + (leadingTerms q).totalDegree)
            (max ((leadingTerms p) * wq).totalDegree (wp * wq).totalDegree) :=
        (max_le_max (totalDegree_mul _ _) (le_refl _))
      _ ≤
          max (wp.totalDegree + (leadingTerms q).totalDegree)
            (max ((leadingTerms p).totalDegree + wq.totalDegree)
              (wp.totalDegree + wq.totalDegree)) :=
        (max_le_max (le_refl _) (max_le_max (totalDegree_mul _ _) (totalDegree_mul _ _)))
      _ < p.totalDegree + q.totalDegree := ?_
    simp only [totalDegree_leadingTerms, max_lt_iff, add_lt_add_iff_right, add_lt_add_iff_left]
    exact ⟨tp, tq, add_lt_add tp tq⟩

--TODO reinterpret this as a hom in this case
theorem totalDegree_mul_eq {S : Type _} [CommRing S] [IsDomain S] {p q : MvPolynomial ι S}
    (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).totalDegree = p.totalDegree + q.totalDegree :=
  by
  rw [← totalDegree_leadingTerms, ← totalDegree_leadingTerms p, ← totalDegree_leadingTerms q,
    leadingTerms_mul, IsHomogeneous.totalDegree]
  apply IsHomogeneous.mul <;> simp [isHomogeneous_leadingTerms]
  apply mul_ne_zero (leadingTerms_ne_zero hp) (leadingTerms_ne_zero hq)

end LeadingTerms

theorem homogenization_add_of_totalDegree_eq (i : ι) (p q : MvPolynomial ι R)
    (h : p.totalDegree = q.totalDegree) (hpq : p.totalDegree = (p + q).totalDegree) :
    (p + q).homogenization i = p.homogenization i + q.homogenization i := by
  dsimp [homogenization]
  rw [Finsupp.mapDomain_add, ← h, ← hpq]

theorem homogenization_mul {S : Type _} [CommRing S] [IsDomain S] (i : ι) (p q : MvPolynomial ι S) :
    -- TODO is this cond needed?
            --(hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
      (p * q).homogenization i = p.homogenization i * q.homogenization i := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [homogenization, homogenization, homogenization, totalDegree_mul_eq hp hq, ←
    Finsupp.sum_single p, ← Finsupp.sum_single q, Finsupp.mapDomain_sum, Finsupp.mapDomain_sum]
  erw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finsupp.single_add, Finsupp.sum_single, monomial_mul]
  rw [Finsupp.mapDomain_finset_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mem_product] at ha
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  simp_rw [single_eq_monomial]
  simp only [Finsupp.single_add, monomial_mul]
  erw [Finsupp.mapDomain_single]
  congr 1
  rw [Finsupp.sum_add_index]
  simp only [Finsupp.single_add, Finsupp.single_tsub]
  ext j
  simp only [Pi.add_apply, Finsupp.coe_add, Finsupp.coe_tsub, Pi.sub_apply]
  classical
  have : ∀ {f s p q fs ss : ℕ} (_ : fs ≤ p) (_ : ss ≤ q),
      f + s + (p + q - (fs + ss)) = f + (p - fs) + (s + (q - ss)) := by
    intros f s p q fs ss hP hQ
    zify [add_le_add hP hQ, hP, hQ]
    ring
  refine' this _ _ <;> rw [Finsupp.single_apply] <;> split_ifs with h
  · simp only [h, Finsupp.single_eq_same]
    convert Finset.le_sup (α := ℕ) ha.left
    rfl
  · simp
  · simp only [h, Finsupp.single_eq_same]
    convert Finset.le_sup (α := ℕ) ha.right
    rfl
  · simp
  · intro i _; rfl
  · intro i; simp

section DangerousInstance

attribute [local instance] MvPolynomial.unique

@[simp]
theorem homogenization_X_add_C {i j : ι} (r : R) :
    (X j + C r : MvPolynomial ι R).homogenization i = X j + C r * X i := by
  nontriviality R
  have : (X j + C r).totalDegree = 1 := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt]
    · exact totalDegree_X _
    · simp only [totalDegree_C, totalDegree_X, Nat.lt_one_iff]
  erw [homogenization, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  simp only [tsub_zero, Finsupp.sum_zero_index, Finsupp.sum_single_index, this, add_zero,
    Finsupp.single_zero, zero_add, single_eq_monomial]
  rw [X, X, ← C_mul_X_pow_eq_monomial, pow_one]
  congr
  simp

@[simp]
theorem homogenization_X_sub_C {R : Type _} [CommRing R] {i j : ι} (r : R) :
    (X j - C r : MvPolynomial ι R).homogenization i = X j - C r * X i := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← C_neg, homogenization_X_add_C, C_neg, neg_mul]

@[simp]
theorem homogenization_X_pow_add_C {i j : ι} {n : ℕ} (hn : 0 < n) (r : R) :
    (X j ^ n + C r : MvPolynomial ι R).homogenization i = X j ^ n + C r * X i ^ n :=
  by
  nontriviality R
  have : totalDegree (X j ^ n + C r) = n := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt]
    · exact totalDegree_X_pow _ _
    · simp only [totalDegree_C, totalDegree_X_pow, hn]
  erw [homogenization, Finsupp.mapDomain_add]
  erw [AddMonoidAlgebra.single_pow]
  erw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  simp only [tsub_zero, Finsupp.sum_zero_index, Finsupp.sum_single_index, zero_add,
    single_eq_monomial, one_pow, mul_one, Finsupp.smul_single', Finsupp.single_tsub]
  congr
  · rw [totalDegree_add_eq_left_of_totalDegree_lt]
    simp [one_ne_zero]
    simp [one_ne_zero, hn]
  · convert (C_mul_X_pow_eq_monomial (R := R)).symm
    rw [← C_mul_X_pow_eq_monomial]
    simp [this]

@[simp]
theorem homogenization_X_pow_sub_C {R : Type _} [CommRing R] {i j : ι} {n : ℕ} (hn : 0 < n)
    (r : R) : (X j ^ n - C r : MvPolynomial ι R).homogenization i = X j ^ n - C r * X i ^ n := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← C_neg, homogenization_X_pow_add_C hn, C_neg, neg_mul]

@[simp]
theorem homogenization_X_pow_sub_one {R : Type _} [CommRing R] {i j : ι} {n : ℕ} (hn : 0 < n) :
    (X j ^ n - 1 : MvPolynomial ι R).homogenization i = X j ^ n - X i ^ n :=
  by
  convert homogenization_X_pow_sub_C hn (R := R) _
  simp

@[simp]
theorem homogenization_X_pow_add_one {i j : ι} {n : ℕ} (hn : 0 < n) :
    (X j ^ n + 1 : MvPolynomial ι R).homogenization i = X j ^ n + X i ^ n :=
  by
  convert homogenization_X_pow_add_C (R := R) hn _
  simp

end DangerousInstance

end MvPolynomial

namespace MvPolynomial

section

-- generalized version of the unprimed version
theorem support_sum_monomial_subset' [DecidableEq ι] {α : Type _} (S : Finset α) (g : α → ι →₀ ℕ)
    (f : α → R) : support (∑ v in S, monomial (g v) (f v)) ⊆ S.image g :=
  by
  letI := Classical.decEq α
  induction' S using Finset.induction with s S hs hsi
  · simp
  · rw [Finset.sum_insert hs]
    apply Finset.Subset.trans support_add
    apply Finset.union_subset
    · apply Finset.Subset.trans support_monomial_subset _
      rw [Finset.image_insert]
      convert Finset.subset_union_left _ (Finset.image g S)
    · apply Finset.Subset.trans hsi _
      rw [Finset.image_insert]
      exact Finset.subset_insert (g s) (Finset.image g S)


open scoped Pointwise

theorem support_mul' [DecidableEq ι] (p q : MvPolynomial ι R) :
    (p * q).support ⊆ p.support + q.support :=
  by
  -- TODO this was really hard to find, maybe needs a docstring or alias?
  rw [p.as_sum, q.as_sum, Finset.sum_mul_sum]
  simp_rw [monomial_mul]
  rw [support_sum_monomial_coeff, support_sum_monomial_coeff]
  exact Finset.Subset.trans (support_sum_monomial_subset' _ _ _) (Finset.Subset.refl _)

section

open scoped Pointwise

theorem support_one : (1 : MvPolynomial ι R).support ⊆ 0 :=
  Finsupp.support_single_subset

@[simp]
theorem support_one_of_nontrivial [Nontrivial R] : (1 : MvPolynomial ι R).support = 0 :=
  Finsupp.support_single_ne_zero _ one_ne_zero

end

variable [DecidableEq ι]

theorem support_prod (P : Finset (MvPolynomial ι R)) : (P.prod id).support ⊆ P.sum support := by
  classical
  induction' P using Finset.induction with p S hS hSi
  · simp only [prod_empty, sum_empty]; exact support_one
  rw [Finset.prod_insert hS, Finset.sum_insert hS]
  simp only [id.def]
  refine' Finset.Subset.trans (support_mul' _ _) _
  convert Finset.add_subset_add (Finset.Subset.refl _) hSi

end

theorem degreeOf_eq_zero_iff (i : ι) (p : MvPolynomial ι R) :
    degreeOf i p = 0 ↔ ∀ j : ι →₀ ℕ, j ∈ p.support → j i = 0 :=
  by
  rw [degreeOf_eq_sup]
  apply Iff.intro
  · intro h j hj
    apply Nat.eq_zero_of_le_zero
    rw [← h]
    apply Finset.le_sup hj
  · intro h
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro m hm
    rw [h m hm]

theorem prod_contains_no (i : ι) (P : Finset (MvPolynomial ι R))
    (hp : ∀ (p : MvPolynomial ι R) (_ : p ∈ P) (j) (_ : j ∈ p.support), (j : ι → ℕ) i = 0) (j)
    (hjp : j ∈ (P.prod id).support) : (j : ι → ℕ) i = 0 :=
  by
  apply (degreeOf_eq_zero_iff i (P.prod id)).1 _ j hjp
  revert hp
  refine' Finset.cons_induction_on P _ _
  · intro _
    simp only [prod_empty, ← C_1, degreeOf_C]
  · intro a s has hs
    intro hp
    rw [prod_cons]
    apply Nat.eq_zero_of_le_zero
    apply le_trans (degreeOf_mul_le _ _ _)
    rw [hs]
    · simp only [id.def, add_zero, le_zero_iff]
      exact (degreeOf_eq_zero_iff _ _).2 (hp a (mem_cons_self _ _))
    · intro p hps m hmp
      apply hp p _ m hmp
      simp only [hps, mem_cons, or_true_iff]

open scoped BigOperators

theorem homogenization_prod {σ S : Type _} [CommRing S] [IsDomain S] (i : ι)
    (P : σ → MvPolynomial ι S) (L : Finset σ) :
    (∏ l in L, P l).homogenization i = ∏ l in L, (P l).homogenization i := by
  classical
  induction' L using Finset.induction with p S hS hSi
  · simp
  simp only [Finset.prod_insert hS]
  rw [homogenization_mul]
  rw [hSi]

theorem homogenization_prod_id {S : Type _} [CommRing S] [IsDomain S] (i : ι)
    (P : Finset (MvPolynomial ι S)) :
    (P.prod id).homogenization i = P.prod fun p => p.homogenization i := by
  classical
  induction' P using Finset.induction with p S hS hSi
  · simp
  simp only [Finset.prod_insert hS]
  rw [homogenization_mul]
  rw [hSi]
  rw [id.def]

end MvPolynomial
