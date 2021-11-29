/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.mv_polynomial.comm_ring
import data.set.finite
import ring_theory.polynomial.homogeneous
import ring_theory.polynomial.basic
import tactic.omega

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

variables {R ι : Type*} [comm_semiring R]
open mv_polynomial

open_locale big_operators
noncomputable theory
namespace mv_polynomial

section finsupp

-- TODO can any assumptions be weakened
-- TODO version with monoid hom?
lemma finsupp.sum_update_add {α β : Type*} [add_comm_monoid α] [add_comm_monoid β]
  (f : ι →₀ α) (i : ι) (a : α) (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
  (hgg : ∀ (a : ι) (b₁ b₂ : α), g a (b₁ + b₂) = g a b₁ + g a b₂) :
  (f.update i a).sum g + g i (f i) = f.sum g + g i a :=
begin
  simp_rw finsupp.update_eq_erase_add_single,
  rw finsupp.sum_add_index hg hgg,
  conv_rhs {rw ← finsupp.update_self f i},
  simp_rw finsupp.update_eq_erase_add_single,
  rw finsupp.sum_add_index hg hgg,
  rw add_assoc,
  rw add_assoc,
  congr' 1,
  rw add_comm,
  rw finsupp.sum_single_index (hg _),
  rw finsupp.sum_single_index (hg _),
end

end finsupp

-- TODO decide if we should make this fix things with X i in already, or have assumptions that X i
-- does not appear everywhere
-- TODO make this change and instead of update simply add to the i component the amount needed
-- this will have better properties (like being idempotent)

/-- The homogenization of a multivariate polynomial at a single variable. -/
def homogenization (i : ι) (p : mv_polynomial ι R) :
  mv_polynomial ι R :=
-- ∑ j in p.support, monomial (j + finsupp.single i (p.total_degree - (j i))) (p.coeff j)
finsupp.map_domain (λ j, j + finsupp.single i (p.total_degree - j.sum (λ _ m, m))) p
-- begin
--   intros x hx y hy hxy,
--   simp at *,
--   ext,
--   have : x.update i (p.total_degree - x.sum (λ (_x : ι) (m : ℕ), m)) a =
--     y.update i (p.total_degree - y.sum (λ (_x : ι) (m : ℕ), m)) a,
--   from congr_fun (congr_arg coe_fn hxy) a,
--   simp at this,
--   by_cases hai : a = i,
--   { subst hai,
--     simp at this,
--     have hx : x.sum (λ (_x : ι) (m : ℕ), m) ≤ p.total_degree,
--     sorry,
--     have hy : y.sum (λ (_x : ι) (m : ℕ), m) ≤ p.total_degree,
--     sorry,
--     have : x.sum (λ (_x : ι) (m : ℕ), m) = y.sum (λ (_x : ι) (m : ℕ), m),
--     sorry,
--     apply_fun (λ K, K.sum (λ _ m, m)) at hxy,
--     sorry,
--     --rw finsupp.sum_update,
--     -- simp at hxy,
--     --apply sub_eq_sub,
--     },
--   { simpa [hai], },
-- end

-- lemma total_degree_add {p q : mv_polynomial ι R} (h : p.total_degree = p.total_degree) :=


-- TODO mathlib
@[simp] lemma support_eq_empty {f : mv_polynomial ι R} : f.support = ∅ ↔ f = 0 :=
finsupp.support_eq_empty

@[simp] lemma finsupp.support_map_domain {α β M : Type*} [add_comm_monoid M]
  (f : α ↪ β) (v : α →₀ M) : (finsupp.map_domain f v).support ⊆ v.support.map f :=
begin
  classical,
  rw finsupp.map_domain,
  refine finset.subset.trans finsupp.support_sum _,
  simp only [finsupp.mem_support_iff, finset.bUnion_subset_iff_forall_subset, ne.def],
  intros x hx,
  apply finset.subset.trans finsupp.support_single_subset,
  simp [hx],
end

-- lemma support_homogenization (i : ι) (p : mv_polynomial ι R)
--   (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : (p.homogenization i).support = p.support.image sorry :=
-- begin
--   rw homogenization,
--   apply finsupp.support_map_domain _ _ _,
-- end

@[simp]
lemma homogenization_zero (i : ι) : (0 : mv_polynomial ι R).homogenization i = 0 :=
by simp [homogenization]

-- TODO this is probably useless
-- lemma map_domain_one {α β M : Type*} [has_zero β] [has_zero α] [has_one M]
--   [add_comm_monoid M] {f : α → β} (hf : f 0 = 0) :
--   finsupp.map_domain f (finsupp.single 0 1 : α →₀ M) = (finsupp.single 0 1 : β →₀ M) :=
-- by simp [hf]

-- TODO maybe instead prove this via is_homogeneous_one
@[simp]
lemma homogenization_one (i : ι) : (1 : mv_polynomial ι R).homogenization i = 1 :=
begin
  simp only [homogenization, total_degree_one, zero_tsub, add_zero, finsupp.single_zero],
  erw finsupp.map_domain_single,
  -- erw map_domain_one,
  refl,
end

@[simp]
lemma homogenization_C (i : ι) (c : R) : (C c : mv_polynomial ι R).homogenization i = C c :=
begin
  simp only [homogenization, total_degree_C, zero_tsub],
  convert finsupp.map_domain_single,
  rw single_eq_monomial,
  have : (0 : ι →₀ ℕ) i = 0,
  { simp only [finsupp.coe_zero, pi.zero_apply], },
  rw [← this],
  simp,
end

lemma total_degree_monomial (s : ι →₀ ℕ) {r : R} (hr : r ≠ 0) :
  total_degree (monomial s r) = s.sum (λ _ e, e) :=
begin
  classical,
  simp [total_degree, support_monomial, if_neg, hr],
end

@[simp]
lemma homogenization_monomial (i : ι) (s : ι →₀ ℕ) (r : R) :
  (monomial s r : mv_polynomial ι R).homogenization i = monomial s r :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  erw [homogenization, finsupp.map_domain_single, single_eq_monomial, total_degree_monomial _ hr,
    tsub_self],
  simp,
end

-- TODO name this
lemma aux {i : ι} {p : mv_polynomial ι R} {x : ι →₀ ℕ} (hp : x ∈ p.support) :
  (x + finsupp.single i (p.total_degree - x.sum (λ _ m, m))).sum (λ _ m, m) = p.total_degree :=
begin
  rw finsupp.sum_add_index,
  rw [finsupp.sum_single_index],
  rw [add_tsub_cancel_iff_le],
  exact finset.le_sup hp,
  refl,
  intro, refl,
  intros, refl,
end

lemma is_homogeneous_homogenization (i : ι) (p : mv_polynomial ι R) :
  (p.homogenization i).is_homogeneous p.total_degree :=
begin
  letI := classical.dec_eq ι,
  rw homogenization,
  intros d hd,
  rw [finsupp.map_domain, finsupp.sum, coeff_sum] at hd,
  simp_rw [single_eq_monomial, coeff_monomial] at hd,
  contrapose! hd,
  have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.support),
    ¬ x + finsupp.single i (p.total_degree - x.sum (λ (_x : ι) (m : ℕ), m)) = d,
  { intros x hx hh,
    apply hd,
    rw ← hh,
    change (x + finsupp.single i (p.total_degree - x.sum (λ _ m, m))).sum (λ _ m, m) = _,
    rw aux hx, },
  conv in (ite _ _ _)
  { rw [if_neg (this x H)], },
  simp,
end

lemma homogenization_of_is_homogeneous (n : ℕ) (i : ι) (p : mv_polynomial ι R)
  (hp : p.is_homogeneous n) : p.homogenization i = p :=
begin
  by_cases hpn : p = 0,
  { simp [hpn], },
  rw homogenization,
  have := (hp.total_degree hpn).symm,
  subst this,
  rw is_homogeneous at hp,
  have : ∀ x (hx : x ∈ p.support),
    (λ (j : ι →₀ ℕ), j + finsupp.single i (p.total_degree - j.sum (λ (_x : ι) (m : ℕ), m))) x = x,
  { intros x hx,
    simp only [add_right_eq_self, finsupp.single_eq_same, tsub_eq_zero_iff_le, finsupp.single_tsub,
      finsupp.single_le_iff],
    rw ← hp (mem_support_iff.mp hx),
    exact le_refl _, },
  rw finsupp.map_domain_congr this,
  -- simp,
  erw finsupp.map_domain_id,
  -- TODO there should be a simp lemma version of this for λ x, x so simp works
end

lemma homogenization_idempotent (i : ι) (p : mv_polynomial ι R) :
  (p.homogenization i).homogenization i = p.homogenization i :=
begin
  classical,
  apply homogenization_of_is_homogeneous p.total_degree,
  exact is_homogeneous_homogenization _ _,
end

namespace finsupp
open finsupp

-- TODO want something like this but unsure what
lemma map_domain_apply' {α β M : Type*} [add_comm_monoid M] (S : set α) {f : α → β} (x : α →₀ M)
  (hS : (x.support : set α) ⊆ S) (hf : set.inj_on f S) {a : α} (ha : a ∈ S) :
  finsupp.map_domain f x (f a) = x a :=
begin
  classical,
  rw finsupp.map_domain,
  simp only [finsupp.sum_apply],
  rw finsupp.sum,
  simp_rw finsupp.single_apply,
  have : ∀ (a_1 : α) (ha1 : a_1 ∈ x.support),
    (if f a_1 = f a then x a_1 else 0) = (if f a_1 = f a then x a else 0),
  { intros a_1 ha_1,
    split_ifs with hh,
    rw hf _ ha hh,
    exact hS ha_1,
    refl, },
  conv in (ite _ _ _)
  { rw [this _ H], },
  by_cases ha : a ∈ x.support,
  rw ← finset.add_sum_erase _ _ ha,
  simp only [if_true, eq_self_iff_true],
  convert add_zero _,
  have : ∀ i ∈ x.support.erase a, f i ≠ f a,
  { intros i hi,
    have hix : i ∈ x.support,
    exact finset.mem_of_mem_erase hi,
    have hia : i ≠ a,
    exact finset.ne_of_mem_erase hi,
    exact hia ∘ (hf (hS hix) (hS ha)), },
  conv in (ite _ _ _)
  { rw if_neg (this x H), },
  simp only [finset.sum_const_zero],
  simp at ha,
  simp [ha],
end

lemma map_domain_injective' {α β M : Type*} [add_comm_monoid M] (S : set α) {f : α → β}
  (hf : set.inj_on f S) :
  set.inj_on (finsupp.map_domain f : (α →₀ M) → (β →₀ M)) {w | (w.support : set α) ⊆ S} :=
begin
  assume v₁ hv₁ v₂ hv₂ eq, ext a,
  have : finsupp.map_domain f v₁ (f a) = finsupp.map_domain f v₂ (f a), { rw eq },
  simp at hv₁ hv₂,
  classical,
  have hu : (v₁.support ∪ v₂.support : set α) ⊆ S := set.union_subset hv₁ hv₂,
  by_cases h : a ∈ v₁.support ∪ v₂.support,
  { rwa [map_domain_apply' S _ hv₁ hf _,
         map_domain_apply' S _ hv₂ hf _] at this,
    apply hu,
    norm_cast,
    exact h,
    apply hu,
    norm_cast,
    exact h, },
  { simp at h,
    push_neg at h,
    simp [h], },
  -- rw [finsupp.map_domain_apply hf, finsupp.map_domain_apply hf] at this,
end
end finsupp

lemma homogenization_ne_zero_of_ne_zero (i : ι) {p : mv_polynomial ι R} (hp : p ≠ 0)
  (hjp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : p.homogenization i ≠ 0 :=
begin
  intro h,
  apply hp,
  have : set.inj_on (λ j : ι →₀ ℕ, j + finsupp.single i (p.total_degree - j.sum (λ _ m, m)))
          {w | w i = 0},
  { intros t ht y hy hh,
    simp only [set.mem_set_of_eq] at hh hy ht,
    ext a,
    have : (t + finsupp.single i (p.total_degree - t.sum (λ _ m, m))) a =
           (y + finsupp.single i (p.total_degree - y.sum (λ _ m, m))) a,
    { rw hh, },
    simp only [finsupp.coe_add, pi.add_apply] at this,
    classical,
    rw [finsupp.single_apply, finsupp.single_apply] at this,
    split_ifs at this with hia,
    { rw [← hia, ht, hy], },
    { simpa, }, },
  refine finsupp.map_domain_injective' _ this _ (by simp) h,
  intros x hx,
  rw [set.mem_set_of_eq, hjp x hx],
  -- refine finsupp.map_domain_injective _ h,
  -- intros x y hxy,
  -- simp at hxy,
  -- -- TODO something like this but this isnt exactly true
  -- sorry,
end

-- TODO this can follow from previous
lemma total_degree_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  --it's not needed, I am keeping as comment since I don't why it's here
  (p.homogenization i).total_degree = p.total_degree :=
begin
  classical,
  by_cases hp : p = 0,
  { simp [hp], },
  apply is_homogeneous.total_degree,
  refine is_homogeneous_homogenization _ _,
  exact (homogenization_ne_zero_of_ne_zero _ hp h),
  -- rw total_degree,
  -- have : (homogenization i p).support.nonempty,
  -- { simp [homogenization],
  --   sorry,
  --    },
  -- rw ← finset.sup'_eq_sup this,
  -- rw finset.nonempty.sup'_eq_cSup_image,
  -- suffices : (λ (s : ι →₀ ℕ), s.sum (λ (n : ι) (e : ℕ), e)) '' ↑((homogenization i p).support) =
  --   {p.total_degree},
  -- { simp [this], },
  -- refine set.eq_singleton_iff_unique_mem.mpr _,
  -- split,
  -- { simp, sorry, },
  -- { simp, sorry, },
end

section leading_terms
-- TODO is this the best def?
/-- The sum of the monomials of highest degree of a multivariate polynomial. -/
def leading_terms (p : mv_polynomial ι R) : mv_polynomial ι R :=
homogeneous_component p.total_degree p

lemma leading_terms_apply (p : mv_polynomial ι R) : p.leading_terms =
  ∑ d in p.support.filter (λ d, ∑ i in d.support, d i = p.total_degree), monomial d (coeff d p) :=
homogeneous_component_apply _ _
-- (p.support.filter (λ s : ι →₀ ℕ, s.sum (λ _ e, e) = p.total_degree)).sum $
--   λ s, monomial s (p.coeff s)

@[simp]
lemma leading_terms_zero : (0 : mv_polynomial ι R).leading_terms = 0 :=
by simp [leading_terms]

lemma finset.filter_eq_self_iff {α : Type*} (S : finset α) (h : α → Prop) [decidable_pred h] :
  S.filter h = S ↔ ∀ s ∈ S, h s :=
begin
  cases S,
  simp only [finset.filter, finset.mem_mk, multiset.filter_eq_self],
end

-- TODO for non-zero polys this is true that p.lead = p iff p.is_homogenous n for a fixed n
-- TODO generalize to p.homog comp = n
lemma leading_terms_eq_self_iff_is_homogeneous (p : mv_polynomial ι R) :
  p.leading_terms = p ↔ p.is_homogeneous p.total_degree :=
begin
  split; intro h,
  { rw is_homogeneous,
    contrapose! h,
    rcases h with ⟨h_w, h_h₁, h_h₂⟩,
    rw [leading_terms, ne.def, mv_polynomial.ext_iff],
    push_neg,
    use h_w,
    classical,
    change ¬ h_w.sum (λ (_x : ι) (e : ℕ), e) = p.total_degree at h_h₂,
    simp only [h_h₁.symm, coeff_homogeneous_component, exists_prop, and_true, ne.def, not_false_iff,
      not_forall, ite_eq_left_iff],
    convert h_h₂, },
  { rw [leading_terms_apply],
    rw (_ : p.support.filter (λ (s : ι →₀ ℕ), ∑ (i : ι) in s.support, s i = p.total_degree)
            = p.support),
    { rw support_sum_monomial_coeff p, },
    { rw finset.filter_eq_self_iff,
      intros s hs,
      rw [mem_support_iff] at hs,
      rw ← h hs, }, },
end

@[simp]
lemma leading_terms_C (r : R) : (C r : mv_polynomial ι R).leading_terms = C r :=
begin
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_C _ _,
  simp,
end

@[simp]
lemma leading_terms_monomial (s : ι →₀ ℕ) (r : R) : (monomial s r).leading_terms = monomial s r :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_monomial _ _ _ _,
  simpa [total_degree_monomial _ hr]
end

section dangerous_instance
local attribute [instance] mv_polynomial.unique
@[simp]
lemma leading_terms_X (s : ι) : (X s : mv_polynomial ι R).leading_terms = X s :=
begin
  nontriviality R,
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_X _ _,
  exact total_degree_X _,
end
end dangerous_instance

lemma is_homogeneous_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.is_homogeneous p.total_degree :=
homogeneous_component_is_homogeneous (total_degree p) p

lemma exists_coeff_ne_zero_total_degree {p : mv_polynomial ι R} (hp : p ≠ 0) :
  ∃ (v : ι →₀ ℕ), v.sum (λ _ e, e) = p.total_degree ∧ p.coeff v ≠ 0 :=
begin
  obtain ⟨b, hb₁, hb₂⟩ := p.support.exists_mem_eq_sup (finsupp.support_nonempty_iff.mpr hp)
    (λ (m : ι →₀ ℕ), m.to_multiset.card),
  use b,
  split,
  { rw ← total_degree_eq p at hb₂,
    rw hb₂,
    dsimp, -- TODO break this out as a lemma
    funext m,
    exact (finsupp.card_to_multiset _).symm, },
  { exact mem_support_iff.mp hb₁, },
end

@[simp] lemma support_zero : (0 : mv_polynomial ι R).support = ∅ := finsupp.support_zero

lemma support_add_eq [decidable_eq ι] {g₁ g₂ : mv_polynomial ι R}
  (h : disjoint g₁.support g₂.support) : (g₁ + g₂).support = g₁.support ∪ g₂.support :=
finsupp.support_add_eq h

lemma add_ne_zero_of_ne_zero_of_support_disjoint [decidable_eq ι] (p q : mv_polynomial ι R)
  (hp : p ≠ 0) (h : disjoint p.support q.support) : p + q ≠ 0 :=
begin
  contrapose! hp,
  have := congr_arg support hp,
  rw [support_zero, support_add_eq h, finset.union_eq_empty_iff, -- TODO should this be simp?
    mv_polynomial.support_eq_empty] at this,
  exact this.left,
end

@[simp] lemma monomial_eq_zero (a : ι →₀ ℕ) (b : R) : monomial a b = 0 ↔ b = 0 :=
finsupp.single_eq_zero

lemma support_sum_monomial_subset (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
  support (∑ v in S, monomial v (f v)) ⊆ S :=
begin
  classical,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  { rw finset.sum_insert hs,
    apply finset.subset.trans support_add,
    apply finset.union_subset,
    { apply finset.subset.trans support_monomial_subset (finset.subset_union_left _ S), },
    { apply finset.subset.trans hsi (finset.subset_insert _ _), }, },
end

-- TODO probably other versions of this lemma for mathlib
lemma ite_subset_union {α : Type*} [decidable_eq α] (s s' : finset α) (P : Prop) [decidable P] :
  ite P s s' ⊆ s ∪ s' :=
begin
  split_ifs,
  exact finset.subset_union_left s s',
  exact finset.subset_union_right s s',
end

-- TODO probably there is a better proof?
lemma sum_monomial_ne_zero_of_exists_mem_ne_zero (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R)
  (h : ∃ (s) (hs : s ∈ S), f s ≠ 0) : ∑ (s : ι →₀ ℕ) in S, monomial s (f s) ≠ 0 :=
begin
  letI := classical.dec_eq ι,
  letI := classical.dec_eq R,
  induction S using finset.induction with s S hs hsi,
  { simpa using h, },
  rw finset.sum_insert hs,
  simp only [exists_prop, finset.mem_insert] at h,
  rcases h with ⟨h, rfl | h_h_left, h_h_right⟩,
  { apply add_ne_zero_of_ne_zero_of_support_disjoint,
    { simpa, },
    { simp only [support_monomial, h_h_right, not_not, mem_support_iff, if_false,
        finset.disjoint_singleton_left],
      rw coeff_sum,
      simp_rw [coeff_monomial],
      conv in (ite _ _ _)
      { rw if_neg (ne_of_mem_of_not_mem H hs : ¬ x = h), }, -- using classical makes this line fail
      simp, }, },
  { rw add_comm,
    apply add_ne_zero_of_ne_zero_of_support_disjoint,
    { apply hsi ⟨h, h_h_left, h_h_right⟩, },
    { simp only [support_monomial],
      apply finset.disjoint_of_subset_right,
      exact ite_subset_union _ _ _,
      simp only [finset.disjoint_singleton_right, finset.empty_union, not_not, mem_support_iff],
      rw coeff_sum,
      simp_rw [coeff_monomial],
      conv in (ite _ _ _)
      { rw if_neg (ne_of_mem_of_not_mem H hs : ¬ x = s), }, -- using classical makes this line fail
      simp, }, },
end

lemma leading_terms_ne_zero {p : mv_polynomial ι R} (hp : p ≠ 0) : p.leading_terms ≠ 0 :=
begin
  classical,
  rw leading_terms_apply,
  apply sum_monomial_ne_zero_of_exists_mem_ne_zero,
  simp only [exists_prop, mem_support_iff, finset.mem_filter],
  convert exists_coeff_ne_zero_total_degree hp,
  ext v,
  change v.sum (λ (_x : ι) (e : ℕ), e) with v.support.sum v,
  simp [and_comm],
end

@[simp]
lemma total_degree_homogenous_component_of_ne_zero {n : ℕ} {p : mv_polynomial ι R}
  (hp : homogeneous_component n p ≠ 0) :
  (homogeneous_component n p).total_degree = n :=
is_homogeneous.total_degree (homogeneous_component_is_homogeneous n p) hp

@[simp]
lemma total_degree_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.total_degree = p.total_degree :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  exact total_degree_homogenous_component_of_ne_zero (leading_terms_ne_zero hp),
end

-- TODO generalize this to homogeneous component idempotent?
lemma leading_terms_idempotent (p : mv_polynomial ι R) :
  p.leading_terms.leading_terms = p.leading_terms :=
begin
  rw [leading_terms_eq_self_iff_is_homogeneous, total_degree_leading_terms],
  exact is_homogeneous_leading_terms p,
end

lemma homogeneous_component_add (m  : ℕ) (p q : mv_polynomial ι R) :
  homogeneous_component m (p + q) = homogeneous_component m p + homogeneous_component m q :=
by rw [homogeneous_component, linear_map.comp_apply, linear_map.comp_apply, linear_map.comp_apply,
    linear_map.map_add, linear_map.map_add]

-- TODO lol this isn't true
-- lemma homogeneous_component_mul (m n : ℕ) (p q : mv_polynomial ι R) :
--   homogeneous_component (m + n) (p * q) = homogeneous_component m p * homogeneous_component n q :=
-- begin
--   sorry,
-- end

lemma coeff_leading_terms (p : mv_polynomial ι R) (d : ι →₀ ℕ) :
  coeff d p.leading_terms = if ∑ i in d.support, d i = p.total_degree then coeff d p else 0 :=
coeff_homogeneous_component _ _ _

lemma support_homogeneous_component (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support = p.support.filter (λ d, d.sum (λ _ m, m) = n) :=
begin
  rw homogeneous_component,
  simp only [finsupp.restrict_dom_apply, submodule.subtype_apply, function.comp_app,
    linear_map.coe_comp, set.mem_set_of_eq],
  erw ← finsupp.support_filter,
  refl,
end

lemma support_homogeneous_component_subset (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support ⊆ p.support :=
begin
  rw support_homogeneous_component,
  exact finset.filter_subset _ _,
end

lemma support_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.support = p.support.filter (λ d, d.sum (λ _ m, m) = p.total_degree) :=
support_homogeneous_component _ _

lemma support_leading_terms_subset (p : mv_polynomial ι R) : p.leading_terms.support ⊆ p.support :=
support_homogeneous_component_subset _ _

lemma eq_leading_terms_add (p : mv_polynomial ι R) (hp : p.total_degree ≠ 0) :
  ∃ p_rest : mv_polynomial ι R,
    p = p.leading_terms + p_rest ∧ p_rest.total_degree < p.total_degree :=
begin
  letI := classical.dec_eq ι,
  existsi (∑ (v : ι →₀ ℕ) in p.support \ p.leading_terms.support, (monomial v) (coeff v p)),
  split,
  { nth_rewrite 0 p.leading_terms.as_sum,
    have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.leading_terms.support), x.support.sum x = p.total_degree,
    { intros x hx,
      rw support_leading_terms at hx,
      simp at hx,
      exact hx.2, },
    simp_rw coeff_leading_terms,
    conv in (ite _ _ _)
    { rw [if_pos (this x H)], },
    have : p.leading_terms.support ⊆ p.support,
    from support_leading_terms_subset _,
    have : p.leading_terms.support ∩ p.support = p.leading_terms.support,
    { rw finset.inter_eq_left_iff_subset,
      exact this },
    nth_rewrite 0 ← this,
    rw finset.inter_comm,
    rw finset.sum_inter_add_sum_diff,
    exact p.as_sum, },
  { rw total_degree,
    rw finset.sup_lt_iff,
    intros b hb,
    rw support_leading_terms at hb,
    rw ← finset.filter_not at hb, -- TODO this was also hard to find maybe a negated version is good
    have := support_sum_monomial_subset _ _ hb,
    simp only [finset.mem_filter] at this,
    cases this,
    rw total_degree,
    apply lt_of_le_of_ne,
    exact finset.le_sup this_left,
    exact this_right,
    rw [bot_eq_zero],
    exact pos_iff_ne_zero.mpr hp, },
end

lemma finset.sup_eq_bot_iff {α β : Type*} [semilattice_sup β] [order_bot β] (f : α → β)
  (S : finset α) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ :=
begin
  classical,
  induction S using finset.induction with a S haS hi,
  { simp, },
  simp [hi],
end

lemma finset.inf_eq_top_iff {α β : Type*} [semilattice_inf β] [order_top β] (f : α → β)
  (S : finset α) : S.inf f = ⊤ ↔ ∀ s ∈ S, f s = ⊤ :=
@finset.sup_eq_bot_iff _ (order_dual β) _ _ _ _ -- same proof also works

lemma is_homogeneous_of_total_degree_zero {p : mv_polynomial ι R} (hp : p.total_degree = 0) :
  is_homogeneous p 0 :=
begin
  rw total_degree at hp,
  erw finset.sup_eq_bot_iff at hp,
  simp only [mem_support_iff] at hp,
  intros d hd,
  exact hp d hd,
end

lemma support_sdiff_support_subset_support_add [decidable_eq ι] (p q : mv_polynomial ι R) :
  p.support \ q.support ⊆ (p + q).support :=
begin
  intros m hm,
  simp only [not_not, mem_support_iff, finset.mem_sdiff, ne.def] at hm,
  simp [hm.2, hm.1],
end

lemma total_degree_add_of_total_degree_lt (p q : mv_polynomial ι R)
  (h : q.total_degree < p.total_degree) : (p + q).total_degree = p.total_degree :=
begin
  by_cases hp : p = 0,
  { simpa [hp] using h, },
  have := total_degree_add p q,
  rwa max_eq_left_of_lt h at this,
  apply le_antisymm,
  { exact this, },
  classical,
  obtain ⟨b, hb₁, hb₂⟩ := p.support.exists_mem_eq_sup (finsupp.support_nonempty_iff.mpr hp)
    (λ (m : ι →₀ ℕ), m.to_multiset.card),
  have hb : ¬ b ∈ q.support,
  { contrapose! h,
    rw [total_degree_eq p, hb₂, total_degree_eq],
    apply finset.le_sup h, },
  have hbb : b ∈ (p + q).support,
  { apply support_sdiff_support_subset_support_add,
    rw finset.mem_sdiff,
    exact ⟨hb₁, hb⟩, },
  rw [total_degree_eq, hb₂, total_degree_eq],
  exact finset.le_sup hbb,
end

lemma leading_terms_add_of_total_degree_lt (p q : mv_polynomial ι R)
  (h : q.total_degree < p.total_degree) : (p + q).leading_terms = p.leading_terms :=
by rw [leading_terms, leading_terms, total_degree_add_of_total_degree_lt p q h,
  homogeneous_component_add, homogeneous_component_eq_zero _ q h, add_zero]

-- lemma C_mul_eq_smul {r : R} (p : mv_polynomial ι R) : C r * p = r • p :=
-- by rw [C_eq_smul_one, algebra.smul_mul_assoc, one_mul]

lemma homogeneous_component_C_mul (n : ℕ) (p : mv_polynomial ι R) (r : R) :
  homogeneous_component n (C r * p) = C r * homogeneous_component n p :=
begin
  rw homogeneous_component,
  simp only [finsupp.restrict_dom_apply, submodule.subtype_apply, function.comp_app,
    linear_map.coe_comp, set.mem_set_of_eq],
  rw C_mul', -- TODO this has a weird name
  rw finsupp.filter_smul,
  rw C_mul', -- TODO this has a weird name
end

lemma no_zero_smul_divisors.eq_zero_or_eq_zero_iff_smul_eq_zero (R M : Type*) [has_zero R]
  [has_zero M] [smul_with_zero R M] [no_zero_smul_divisors R M] {c : R} {x : M} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
begin
  split; intro h,
  exact eq_zero_or_eq_zero_of_smul_eq_zero h,
  cases h;
  simp [h],
end

--TODO this generalized lemma when distrib_mul_action_with_zero exists?
-- lemma support_smul_eq {α M R : Type*} {_ : monoid_with_zero R} [add_monoid M]
--   [distrib_mul_action_with_zero R M] [no_zero_smul_divisors R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} :
--   (b • g).support = g.support :=
-- begin
--   ext a,
--   simp [finsupp.smul_apply, mem_support_iff, ne.def],
--   simp,
--   rw no_zero_smul_divisors.eq_zero_or_eq_zero_iff_smul_eq_zero,
-- end

lemma finsupp.support_smul_eq {α M R : Type*} [semiring R] [add_comm_monoid M] [module R M]
  [no_zero_smul_divisors R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} :
  (b • g).support = g.support :=
begin
  ext a,
  simp [finsupp.smul_apply, mem_support_iff, ne.def, hb],
end

-- haveI : no_zero_smul_divisors R (mv_polynomial ι R), --TODO add this instance
--TODO maybe this for leading terms and homog
-- lemma homogeneous_s_monomial_mul [no_zero_divisors R] (p : mv_polynomial ι R) (r : R) (x : ι →₀ ℕ) :
  -- (p * monomial x r).leading_terms = p.leading_terms * monomial x r :=
  --TODO also maybe an smul version
@[simp]
lemma leading_terms_C_mul [no_zero_smul_divisors R R] (p : mv_polynomial ι R) (r : R) :
  (C r * p).leading_terms = C r * p.leading_terms :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  have : (C r * p).support = p.support,
  { rw C_mul',
    exact finsupp.support_smul_eq hr, },
  rw [leading_terms, leading_terms, total_degree, this, homogeneous_component_C_mul],
  refl,
end

lemma eq_C_of_total_degree_zero {p : mv_polynomial ι R} (hp : p.total_degree = 0) :
  ∃ r : R, p = C r :=
begin
  letI := classical.dec_eq ι,
  erw finset.sup_eq_bot_iff at hp,
  simp only [mem_support_iff] at hp,
  use coeff 0 p,
  ext,
  by_cases hm : m = 0,
  { simp [hm], },
  rw [coeff_C, if_neg (ne.symm hm)],
  classical,
  by_contradiction h,
  specialize hp m h,
  apply hm,
  rw finsupp.sum at hp, -- TODO this and line below could be a lemma, finsupp.sum_eq_zero_iff?
  simp only [not_imp_self, bot_eq_zero, finsupp.mem_support_iff, finset.sum_eq_zero_iff] at hp,
  ext,
  simp [hp],
end

-- TODO can things be generalized to no_zero_divisors (would require an instance for mv_poly)
-- sadly this adds some imports and requirements not needed in rest of file
@[simp]
lemma leading_terms_mul {S : Type*} [comm_ring S] [is_domain S] (p q : mv_polynomial ι S) :
  (p * q).leading_terms = p.leading_terms * q.leading_terms :=
begin
  by_cases hp : p.total_degree = 0,
  { rcases eq_C_of_total_degree_zero hp with ⟨rp, rfl⟩,
    rw [leading_terms_C_mul, leading_terms_C], },
  by_cases hq : q.total_degree = 0,
  { rcases eq_C_of_total_degree_zero hq with ⟨rq, rfl⟩,
    rw [mul_comm, leading_terms_C_mul, leading_terms_C, mul_comm], },
  have : (p.leading_terms * q.leading_terms).total_degree = p.total_degree + q.total_degree,
  { rw is_homogeneous.total_degree,
    apply is_homogeneous.mul (is_homogeneous_leading_terms p) (is_homogeneous_leading_terms q),
    apply mul_ne_zero,
    { apply leading_terms_ne_zero, -- TODO maybe this can be a lemma ne_zero_of_total_degree_ne_zero
      intro hh,
      subst hh,
      simpa, },
    { apply leading_terms_ne_zero, -- TODO maybe this can be a lemma ne_zero_of_total_degree_ne_zero
      intro hh,
      subst hh,
      simpa, }, },
  rcases eq_leading_terms_add p hp with ⟨wp, hp, tp⟩,
  rw hp,
  rcases eq_leading_terms_add q hq with ⟨wq, hq, tq⟩,
  rw hq,
  simp only [add_mul, mul_add],
  rw [add_assoc, leading_terms_add_of_total_degree_lt, leading_terms_add_of_total_degree_lt,
    leading_terms_add_of_total_degree_lt, leading_terms_idempotent, leading_terms_idempotent,
    leading_terms_eq_self_iff_is_homogeneous],
  { convert is_homogeneous.mul (is_homogeneous_leading_terms _) (is_homogeneous_leading_terms _), },
  { rwa total_degree_leading_terms, },
  { rwa total_degree_leading_terms, },
  { rw this,
    calc _ ≤ max (wp * q.leading_terms).total_degree (p.leading_terms * wq + wp * wq).total_degree :
              total_degree_add _ _
       ... ≤ max (wp * q.leading_terms).total_degree
              (max (p.leading_terms * wq).total_degree (wp * wq).total_degree) :
                max_le_max (le_refl _) (total_degree_add _ _)
       ... ≤ max (wp.total_degree + q.leading_terms.total_degree)
              (max (p.leading_terms * wq).total_degree (wp * wq).total_degree) :
                max_le_max (total_degree_mul _ _) (le_refl _)
       ... ≤ max (wp.total_degree + q.leading_terms.total_degree)
              (max (p.leading_terms.total_degree + wq.total_degree)
                (wp.total_degree + wq.total_degree)) :
                  max_le_max (le_refl _) (max_le_max (total_degree_mul _ _) (total_degree_mul _ _))
       ... < p.total_degree + q.total_degree : _,
    simp only [total_degree_leading_terms, max_lt_iff, add_lt_add_iff_right, add_lt_add_iff_left],
    exact ⟨tp, tq, add_lt_add tp tq⟩, },
end

lemma total_degree_mul_eq {S : Type*} [comm_ring S] [is_domain S] {p q : mv_polynomial ι S}
  (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).total_degree = p.total_degree + q.total_degree :=
begin
  rw [← total_degree_leading_terms, ← total_degree_leading_terms p, ← total_degree_leading_terms q,
    leading_terms_mul, is_homogeneous.total_degree],
  apply is_homogeneous.mul;
  simp [is_homogeneous_leading_terms],
  apply mul_ne_zero (leading_terms_ne_zero hp) (leading_terms_ne_zero hq),
end

end leading_terms

lemma homogenization_add_of_total_degree_eq (i : ι) (p q : mv_polynomial ι R)
  (h : p.total_degree = q.total_degree) (hpq : p.total_degree = (p + q).total_degree) :
  (p + q).homogenization i = p.homogenization i + q.homogenization i :=
by simp only [homogenization, finsupp.map_domain_add, ←h, ←hpq]

lemma auxx (f s p q fs ss : ℕ) (hp : fs ≤ p) (hp : ss ≤ q) :
  f + s + (p + q - (fs + ss)) = f + (p - fs) + (s + (q - ss)) := by omega

lemma homogenization_mul {S : Type*} [comm_ring S] [is_domain S] (i : ι) (p q : mv_polynomial ι S) :
  -- TODO is this cond needed?
  --(hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
  (p * q).homogenization i = p.homogenization i * q.homogenization i :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  by_cases hq : q = 0,
  { simp [hq], },
  rw [homogenization, homogenization, homogenization, total_degree_mul_eq hp hq,
    ← finsupp.sum_single p, ← finsupp.sum_single q, finsupp.map_domain_sum, finsupp.map_domain_sum],
  erw [finset.sum_mul_sum, finset.sum_mul_sum],
  simp only [finsupp.single_add, finsupp.sum_single, monomial_mul],
  rw finsupp.map_domain_finset_sum,
  apply finset.sum_congr rfl,
  intros a ha,
  simp only [finset.mem_product] at ha,
  rw [finsupp.map_domain_single, finsupp.map_domain_single],
  simp_rw [single_eq_monomial],
  simp only [finsupp.single_add, monomial_mul],
  erw finsupp.map_domain_single,
  congr' 1,
  rw finsupp.sum_add_index,
  simp only [finsupp.single_add, finsupp.single_tsub],
  ext j,
  simp only [pi.add_apply, finsupp.coe_add, finsupp.coe_tsub, pi.sub_apply],
  classical,
  refine auxx _ _ _ _ _ _ _ _,
  { rw finsupp.single_apply,
    split_ifs,
    { simp only [h, finsupp.single_eq_same],
      convert finset.le_sup ha.left,
      congr, }, -- TODO what is going on here?
    { simp, }, },
  { rw finsupp.single_apply,
    split_ifs,
    { simp only [h, finsupp.single_eq_same],
      convert finset.le_sup ha.right,
      congr, }, -- TODO what is going on here?
    { simp, }, },
  { intro i, refl, },
  { intro i, simp, },
end

section dangerous_instance
local attribute [instance] mv_polynomial.unique

@[simp]
lemma homogenization_X_add_C {i j : ι} (r : R) :
  (X j + C r : mv_polynomial ι R).homogenization i = X j + C r * X i :=
begin
  nontriviality R,
  have : (X j + C r).total_degree = 1,
  { rw total_degree_add_of_total_degree_lt,
    { exact total_degree_X _, },
    { simp only [total_degree_C, total_degree_X, nat.lt_one_iff], }, },
  erw [homogenization, finsupp.map_domain_add, finsupp.map_domain_single,
    finsupp.map_domain_single],
  simp only [tsub_zero, finsupp.sum_zero_index, finsupp.sum_single_index, this, add_zero,
    finsupp.single_zero, zero_add, single_eq_monomial],
  rw [X, X],
  congr,
  rw [monomial_eq_C_mul_X, pow_one],
  refl,
end

@[simp]
lemma homogenization_X_sub_C {R : Type*} [comm_ring R] {i j : ι} (r : R) :
  (X j - C r : mv_polynomial ι R).homogenization i = X j - C r * X i :=
by rw [sub_eq_add_neg, sub_eq_add_neg, ← C_neg, homogenization_X_add_C,
  C_neg, neg_mul_eq_neg_mul_symm]

lemma support_X_pow [nontrivial R] (s : ι) (n : ℕ) :
  (X s ^ n : mv_polynomial ι R).support = {finsupp.single s n} :=
begin
  classical,
  rw [X, monomial_pow, support_monomial, if_neg, finsupp.smul_single', mul_one],
  { rw [one_pow],
    exact one_ne_zero, },
end

@[simp] lemma total_degree_X_pow {R} [comm_semiring R] [nontrivial R] (s : ι) (n : ℕ) :
  (X s ^ n : mv_polynomial ι R).total_degree = n :=
begin
  rw [total_degree, support_X_pow],
  simp only [finset.sup, finsupp.sum_single_index, finset.fold_singleton, sup_bot_eq],
end

@[simp]
lemma homogenization_X_pow_add_C {i j : ι} {n : ℕ} (hn : 0 < n) (r : R) :
  (X j ^ n + C r : mv_polynomial ι R).homogenization i = X j ^ n + C r * X i ^ n :=
begin
  nontriviality R,
  have : (X j ^ n + C r).total_degree = n,
  { rw total_degree_add_of_total_degree_lt,
    { exact total_degree_X_pow _ _, },
    { simp only [total_degree_C, total_degree_X_pow, hn], }, },
  erw [homogenization, finsupp.map_domain_add],
  erw add_monoid_algebra.single_pow,
  erw [finsupp.map_domain_single,
    finsupp.map_domain_single],
  simp only [tsub_zero, finsupp.sum_zero_index, finsupp.sum_single_index, zero_add,
    single_eq_monomial, one_pow, mul_one, finsupp.smul_single', finsupp.single_tsub],
  congr,
  simp,
  sorry,
  sorry,
end

@[simp]
lemma homogenization_X_pow_sub_C {R : Type*} [comm_ring R] {i j : ι} {n : ℕ} (hn : 0 < n) (r : R) :
  (X j ^ n - C r : mv_polynomial ι R).homogenization i = X j ^ n - C r * X i ^ n :=
by rw [sub_eq_add_neg, sub_eq_add_neg, ← C_neg, homogenization_X_pow_add_C hn,
  C_neg, neg_mul_eq_neg_mul_symm]

end dangerous_instance

end mv_polynomial
section finset_prod
namespace finset

-- Like everything else in this file, for mathlib, theory of add / mul on finsets, API duplicated
-- from the set version

open function
open finset

variables {α : Type*} {β : Type*} {s s₁ s₂ t t₁ t₂ u : finset α} {a b : α} {x y : β}
open_locale pointwise

/-- The set `(1 : finset α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive
/-"The set `(0 : finset α)` is defined as `{0}` in locale `pointwise`. "-/]
protected def has_one [has_one α] : has_one (finset α) := ⟨{1}⟩

localized "attribute [instance] finset.has_one finset.has_zero" in pointwise

@[to_additive]
lemma singleton_one [has_one α] : ({1} : finset α) = 1 := rfl

@[simp, to_additive]
lemma mem_one [has_one α] : a ∈ (1 : finset α) ↔ a = 1 :=
by simp [has_one.one]

@[to_additive]
lemma one_mem_one [has_one α] : (1 : α) ∈ (1 : finset α) := by simp [has_one.one]

@[simp, to_additive]
theorem one_subset [has_one α] : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

@[to_additive]
theorem one_nonempty [has_one α] : (1 : finset α).nonempty := ⟨1, one_mem_one⟩

@[simp, to_additive]
theorem image_one [decidable_eq β] [has_one α] {f : α → β} : image f 1 = {f 1} :=
image_singleton f 1

-- @[simp, to_additive]
-- lemma image2_mul [has_mul α] : finset.image2 has_mul.mul s t = s * t := rfl

-- this is just a symmetrized version of the def, is it needed?
-- TODO why are these names weird
@[to_additive add_image_prod]
lemma image_mul_prod [decidable_eq α] [has_mul α] :
  image (λ x : α × α, x.fst * x.snd) (s.product t) = s * t := rfl

@[simp, to_additive]
lemma image_mul_left [decidable_eq α] [group α] :
  image (λ b, a * b) t = preimage t (λ b, a⁻¹ * b) (assume x hx y hy, (mul_right_inj a⁻¹).mp) :=
begin
  have := @set.image_mul_left _ (t : set α) a _,
  rw ← finset.coe_preimage _ (assume x hx y hy, (mul_right_inj a⁻¹).mp) at this,
  exact_mod_cast this,
end

@[simp, to_additive]
lemma image_mul_right [decidable_eq α] [group α] :
  image (λ a, a * b) t = preimage t (λ a, a * b⁻¹) (assume x hx y hy, (mul_left_inj b⁻¹).mp) :=
begin
  have := @set.image_mul_right _ (t : set α) b _,
  rw ← finset.coe_preimage at this,
  swap,
  intros x hx y hy,
  simp,
  exact_mod_cast this,
end

@[to_additive]
lemma image_mul_left' [decidable_eq α] [group α] :
  image (λ b, a⁻¹ * b) t = preimage t (λ b, a * b) (assume x hx y hy, (mul_right_inj a).mp) :=
by simp

@[to_additive]
lemma image_mul_right' [decidable_eq α] [group α] :
  image (λ a, a * b⁻¹) t = preimage t (λ a, a * b) (assume x hx y hy, (mul_left_inj b).mp) :=
by simp

@[simp, to_additive]
lemma preimage_mul_left_singleton [group α] :
  preimage {b} ((*) a) (assume x hx y hy, (mul_right_inj a).mp) = {a⁻¹ * b} :=
by { classical, rw [← image_mul_left', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_right_singleton [group α] :
  preimage {b} (* a) (assume x hx y hy, (mul_left_inj a).mp) = {b * a⁻¹} :=
by { classical, rw [← image_mul_right', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_left_one [group α] :
  preimage 1 (λ b, a * b) (assume x hx y hy, (mul_right_inj a).mp) = {a⁻¹} :=
by {classical, rw [← image_mul_left', image_one, mul_one] }

@[simp, to_additive]
lemma preimage_mul_right_one [group α] :
  preimage 1 (λ a, a * b) (assume x hx y hy, (mul_left_inj b).mp) = {b⁻¹} :=
by {classical, rw [← image_mul_right', image_one, one_mul] }

@[to_additive]
lemma preimage_mul_left_one' [group α] :
  preimage 1 (λ b, a⁻¹ * b) (assume x hx y hy, (mul_right_inj _).mp) = {a} := by simp

@[to_additive]
lemma preimage_mul_right_one' [group α] :
  preimage 1 (λ a, a * b⁻¹) (assume x hx y hy, (mul_left_inj _).mp) = {b} := by simp

@[simp, to_additive]
lemma mul_singleton [decidable_eq α] [has_mul α] : s * {b} = image (λ a, a * b) s :=
begin
  have := @set.mul_singleton _ (s : set α) b _,
  norm_cast at this,
  rw (by simp : ({b} : set α) = ↑({b} : finset α)) at this,
  exact_mod_cast this,
end

@[simp, to_additive]
lemma singleton_mul [decidable_eq α] [has_mul α] : {a} * t = image (λ b, a * b) t :=
begin
  have := @set.singleton_mul _ (t : set α) a _,
  norm_cast at this,
  rw (by simp : ({a} : set α) = ↑({a} : finset α)) at this,
  exact_mod_cast this,
end

@[simp, to_additive]
lemma singleton_mul_singleton [decidable_eq α] [has_mul α] : ({a} : finset α) * {b} = {a * b} :=
begin
  have := @set.singleton_mul_singleton _ a b _,
  rw (by simp : ({a} : set α) = ↑({a} : finset α)) at this,
  rw (by simp : ({b} : set α) = ↑({b} : finset α)) at this,
  exact_mod_cast this,
end

@[to_additive]
protected lemma mul_comm [decidable_eq α] [comm_semigroup α] : s * t = t * s :=
by exact_mod_cast @set.mul_comm _ (s : set α) t _

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_zero_class` under pointwise operations if `α` is."-/]
protected def mul_one_class [decidable_eq α] [mul_one_class α] : mul_one_class (finset α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..finset.has_one, ..finset.has_mul }

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_semigroup` under pointwise operations if `α` is. "-/]
protected def semigroup [decidable_eq α] [semigroup α] : semigroup (finset α) :=
{ mul_assoc := λ a b c,
    by exact_mod_cast (set.semigroup.mul_assoc : ∀ (a b c : set α), a * b * c = a * (b * c)) a b c,
  ..finset.has_mul }

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_monoid` under pointwise operations if `α` is. "-/]
protected def monoid [decidable_eq α] [monoid α] : monoid (finset α) :=
{ ..finset.semigroup,
  ..finset.mul_one_class }

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_comm_monoid` under pointwise operations if `α` is. "-/]
protected def comm_monoid [decidable_eq α] [comm_monoid α] : comm_monoid (finset α) :=
{ mul_comm := λ _ _, finset.mul_comm, ..finset.monoid }

localized "attribute [instance] finset.mul_one_class finset.add_zero_class finset.semigroup
  finset.add_semigroup finset.monoid finset.add_monoid finset.comm_monoid finset.add_comm_monoid"
  in pointwise

-- TODO there is loads more API in pointwise that could (should) be duplicated?

-- TODO a lemma mem_prod for both set and finset, saying that something is in a product of sets
-- only if it is a product of elements of each


end finset
end finset_prod

namespace mv_polynomial
section

-- generalized version of the unprimed version
lemma support_sum_monomial_subset' [decidable_eq ι] {α : Type*} (S : finset α) (g : α → ι →₀ ℕ)
  (f : α → R) : support (∑ v in S, monomial (g v) (f v)) ⊆ S.image g :=
begin
  letI := classical.dec_eq α,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  { rw finset.sum_insert hs,
    apply finset.subset.trans support_add,
    apply finset.union_subset,
    { apply finset.subset.trans support_monomial_subset _,
      rw finset.image_insert,
      convert finset.subset_union_left _ (finset.image g S), },
    { apply finset.subset.trans hsi _,
      rw finset.image_insert,
      exact finset.subset_insert (g s) (finset.image g S), }, },
end
open_locale pointwise

lemma support_mul' [decidable_eq ι] (p q : mv_polynomial ι R) :
  (p * q).support ⊆ p.support + q.support :=
begin
  -- TODO this was really hard to find, maybe needs a docstring or alias?
  rw [p.as_sum, q.as_sum, finset.sum_mul_sum],
  simp_rw [monomial_mul],
  rw [support_sum_monomial_coeff, support_sum_monomial_coeff],
  exact finset.subset.trans (support_sum_monomial_subset' _ _ _) (finset.subset.refl _),
end

section
open_locale pointwise
@[simp] lemma support_one : (1 : mv_polynomial ι R).support ⊆ 0 :=
finsupp.support_single_subset
-- @[simp] lemma support_one [nontrivial R] : (1 : mv_polynomial ι R).support = 0 :=
-- begin
--   convert (finsupp.support_eq_singleton).mpr _,
--   split,
--   simp,
--   change (1 : R) ≠ 0,
-- end
end

variable [decidable_eq ι]
lemma support_prod (P : finset (mv_polynomial ι R)) : (P.prod id).support ⊆ P.sum support :=
begin
  classical,
  induction P using finset.induction with p S hS hSi,
  { simp [support_X], },
  rw [finset.prod_insert hS, finset.sum_insert hS],
  simp only [id.def],
  refine finset.subset.trans (support_mul' _ _) _,
  convert finset.add_subset_add (finset.subset.refl _) hSi,
end

end

lemma prod_contains_no (i : ι) (P : finset (mv_polynomial ι R))
  (hp : ∀ (p : mv_polynomial ι R) (hp : p ∈ P) (j) (hjp : j ∈ p.support), (j : ι → ℕ) i = 0)
  (j) (hjp : j ∈ (P.prod id).support) :
  (j : ι → ℕ) i = 0 :=
begin
  classical,
  induction P using finset.induction with p S hS hSi generalizing j,
  { simp only [mem_support_iff, finset.prod_empty] at hjp,
    have : j = 0,
    sorry,
    simp [this], },
  { have := support_prod _ hjp,
    rw finset.prod_insert hS at hjp,
    rw finset.sum_insert hS at this,
    rw finset.mem_add at this,
    rcases this with ⟨y, z, hy, hz, hh⟩,
    rw ← hh,
    have := hp _ (finset.mem_insert_self p S) _ hy,
    simp only [pi.add_apply, add_eq_zero_iff, finsupp.coe_add],
    rw hSi _ z _,
    { rw this,
      simp, },
    { intros p hpp j hj,
      exact hp p (finset.mem_insert_of_mem hpp) j hj, },
    sorry,
    -- TODO probably need more lemmas for this still
    -- apply support_prod,
  },
  -- TODO this proof should be simple with `support_prod` we know j is in
  -- { simp only [finset.prod_insert hS, id.def, ne.def] at hjp,
  --   apply hSi, },
end


open_locale big_operators
lemma homogenization_prod {σ S : Type*} [comm_ring S] [is_domain S] (i : ι)
  (P : σ → mv_polynomial ι S) (L : finset σ) :
  (∏ l in L, P l).homogenization i = ∏ l in L, (P l).homogenization i :=
begin
  classical,
  induction L using finset.induction with p S hS hSi,
  { simp, },
  simp only [finset.prod_insert hS],
  rw homogenization_mul,
  rw hSi,
end

lemma homogenization_prod_id {S : Type*} [comm_ring S] [is_domain S] (i : ι)
  (P : finset (mv_polynomial ι S)) :
  (P.prod id).homogenization i = P.prod (λ p, p.homogenization i) :=
begin
  classical,
  induction P using finset.induction with p S hS hSi,
  { simp, },
  simp only [finset.prod_insert hS],
  rw homogenization_mul,
  rw hSi,
  rw [id.def],
end

end mv_polynomial
