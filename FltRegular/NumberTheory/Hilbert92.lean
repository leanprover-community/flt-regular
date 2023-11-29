
import FltRegular.NumberTheory.Cyclotomic.UnitLemmas
import FltRegular.NumberTheory.GaloisPrime
import Mathlib

set_option autoImplicit false
open scoped NumberField nonZeroDivisors
open FiniteDimensional
open NumberField

variable (p : ℕ+) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {k : Type*} [Field k] [NumberField k] (hp : Nat.Prime p)

open FiniteDimensional BigOperators Finset
-- Z[H] module M (rank L) submodule N (rank l) H-stable
-- H cyclic order p
-- M / N is free up to torsion rank r (as an ab group free rank r p)
-- r = r1 + r2 - 1 = NumberField.Units.rank


section thm91
variable
  (G : Type*) {H : Type*} [AddCommGroup G] [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (r : ℕ)
  [DistribMulAction H G] [Module.Free ℤ G] (hf : finrank ℤ G = r * (p - 1))

-- TODO maybe abbrev
local notation3 "A" =>
  MonoidAlgebra ℤ H ⧸ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ H σ) ^ i}

structure systemOfUnits (r : ℕ) [Module A G]
  where
  units : Fin r → G
  linearIndependent : LinearIndependent A units

instance systemOfUnits.instFintype {r}
  [Module A G] -- [IsScalarTower ℤ A G]
  (sys : systemOfUnits (G := G) p σ r) : Fintype (G ⧸ Submodule.span A (Set.range sys.units)) := sorry

def systemOfUnits.index [Module A G] (sys : systemOfUnits p G σ r) :=
  Fintype.card (G ⧸ Submodule.span A (Set.range sys.units))

def systemOfUnits.IsFundamental [Module A G] (h : systemOfUnits p G σ r) :=
  ∀ s : systemOfUnits p G σ r, h.index ≤ s.index

lemma systemOfUnits.IsFundamental.maximal' [Module A G] (S : systemOfUnits p G σ r)
    (hs : S.IsFundamental) (a : systemOfUnits p G σ r) :
    (Submodule.span A (Set.range S.units)).toAddSubgroup.index ≤
      (Submodule.span A (Set.range a.units)).toAddSubgroup.index := by
  convert hs a <;> symm <;> exact Nat.card_eq_fintype_card.symm

@[to_additive]
theorem Finsupp.prod_congr' {α M N} [Zero M] [CommMonoid N] {f₁ f₂ : α →₀ M} {g1 g2 : α → M → N}
    (h : ∀ x, g1 x (f₁ x) = g2 x (f₂ x)) (hg1 : ∀ i, g1 i 0 = 1) (hg2 : ∀ i, g2 i 0 = 1) :
    f₁.prod g1 = f₂.prod g2 := by
  classical
  rw [f₁.prod_of_support_subset (Finset.subset_union_left _ f₂.support) _ (fun i _ ↦ hg1 i),
    f₂.prod_of_support_subset (Finset.subset_union_right f₁.support _) _ (fun i _ ↦ hg2 i)]
  exact Finset.prod_congr rfl (fun x _ ↦ h x)

lemma LinearIndependent.update {ι} [DecidableEq ι] {R} [CommRing R] [Module R G]
    (f : ι → G) (i : ι) (g : G) (σ : R)
    (hσ : σ ∈ nonZeroDivisors R) (hg : σ • g = f i) (hf : LinearIndependent R f):
    LinearIndependent R (Function.update f i g) := by
  classical
  rw [linearIndependent_iff] at hf ⊢
  intros l hl
  have : (Finsupp.total ι G R f) (Finsupp.update (σ • l) i (l i)) = 0
  · rw [← smul_zero σ, ← hl, Finsupp.total_apply, Finsupp.total_apply, Finsupp.smul_sum]
    apply Finsupp.sum_congr'
    · intro x
      simp only [Finsupp.coe_update, Finsupp.coe_smul, Function.update_apply, ite_smul, smul_ite]
      rw [smul_smul, mul_comm σ, ← smul_smul, hg, Pi.smul_apply, smul_eq_mul, ← smul_smul]
      split <;> simp [*]
    · simp
    · simp
  ext j
  have := FunLike.congr_fun (hf (Finsupp.update (σ • l) i (l i)) this) j
  simp only [Finsupp.coe_update, Finsupp.coe_smul, ne_eq, Function.update_apply, Finsupp.coe_zero,
    Pi.zero_apply] at this
  split_ifs at this with hij
  · exact hij ▸ this
  · exact hσ (l j) ((mul_comm _ _).trans this)

@[to_additive]
lemma Subgroup.index_mono {G : Type*} [Group G] {H₁ H₂ : Subgroup G} (h : H₁ < H₂)
  [h₁ : Fintype (G ⧸ H₁)] :
  H₂.index < H₁.index := sorry

namespace systemOfUnits

lemma nontrivial (hr : r ≠ 0) : Nontrivial G := by
    by_contra' h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [FiniteDimensional.finrank_zero_of_subsingleton] at hf
    simp only [ge_iff_le, zero_eq_mul, tsub_eq_zero_iff_le] at hf
    cases hf with
    | inl h => exact hr h
    | inr h => simpa [Nat.lt_succ_iff, h] using not_lt.2 (Nat.prime_def_lt.1 hp).1

lemma bezout [Module A G] {a : A} (ha : a ≠ 0) : ∃ (f : A) (n : ℤ),
        f * a = n := sorry

lemma existence0 [Module A G] : Nonempty (systemOfUnits p G σ 0) := by
    exact ⟨⟨fun _ => 0, linearIndependent_empty_type⟩⟩

lemma ex_not_mem [Module A G] {R : ℕ} (S : systemOfUnits p G σ R) (hR : R < r) :
        ∃ g, ∀ (k : ℤ), ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
    by_contra' h
    sorry

set_option synthInstance.maxHeartbeats 0 in
lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G σ R) (hR : R < r) :
        Nonempty (systemOfUnits p G σ (R + 1)) := by
    obtain ⟨g, hg⟩ := ex_not_mem p G σ r S hR
    refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
    refine LinearIndependent.fin_cons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
    by_contra' ha
    obtain ⟨f, n, Hf⟩ := bezout p G σ ha
    replace hy := congr_arg (f • ·) hy
    simp only at hy
    let mon : Monoid A := inferInstance
    rw [smul_zero, smul_add, smul_smul, Hf, ← eq_neg_iff_add_eq_zero, intCast_smul] at hy
    apply hg n
    rw [hy]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ y.2)

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ r) :  Nonempty (systemOfUnits p G σ R) := by
    induction R with
    | zero => exact existence0 p G σ
    | succ n ih =>
        obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
        exact existence' p G σ r S (lt_of_lt_of_le (Nat.lt.base n) hR)

lemma existence (r) [Module A G] : Nonempty (systemOfUnits p G σ r) := existence'' p G σ r rfl.le

end systemOfUnits

noncomputable
abbrev σA : A := MonoidAlgebra.of ℤ H σ

lemma one_sub_σA_mem : 1 - σA p σ ∈ A⁰ := sorry

lemma one_sub_σA_mem_nonunit : ¬ IsUnit (1 - σA p σ) := sorry

lemma isCoprime_one_sub_σA (n : ℤ) (hn : ¬ (p : ℤ) ∣ n): IsCoprime (1 - σA p σ) n := sorry

namespace fundamentalSystemOfUnits
lemma existence [Module A G] : ∃ S : systemOfUnits p G σ r, S.IsFundamental := by
  obtain ⟨S⟩ := systemOfUnits.existence p G σ r
  have : { a | ∃ S : systemOfUnits p G σ r, a = S.index}.Nonempty := ⟨S.index, S, rfl⟩
  obtain ⟨S', ha⟩ := Nat.sInf_mem this
  use S'
  intro a'
  rw [← ha]
  apply csInf_le (OrderBot.bddBelow _)
  use a'

lemma lemma2 [Module A G] (S : systemOfUnits p G σ r) (hs : S.IsFundamental) (i : Fin r) :
    ∀ g : G, (1 - σA p σ) • g ≠ S.units i := by
  intro g hg
  let S' : systemOfUnits p G σ r := ⟨Function.update S.units i g,
    LinearIndependent.update (hσ := one_sub_σA_mem p σ) (hg := hg) S.linearIndependent⟩
  suffices : Submodule.span A (Set.range S.units) < Submodule.span A (Set.range S'.units)
  · exact (hs.maximal' S').not_lt (AddSubgroup.index_mono (h₁ := S.instFintype) this)
  rw [SetLike.lt_iff_le_and_exists]
  constructor
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hij : i = j
    · rw [← hij, ← hg]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Function.update_same _ _ _⟩)
    · exact Submodule.subset_span ⟨j, Function.update_noteq (Ne.symm hij) _ _⟩
  · refine ⟨g, Submodule.subset_span ⟨i, Function.update_same _ _ _⟩, ?_⟩
    rw [← Finsupp.range_total]
    rintro ⟨l, rfl⟩
    letI := (Algebra.id A).toModule
    letI : SMulZeroClass A A := SMulWithZero.toSMulZeroClass
    letI : Module A (Fin r →₀ A) := Finsupp.module (Fin r) A
    rw [← (Finsupp.total _ _ _ _).map_smul, ← one_smul A (S.units i),
      ← Finsupp.total_single A (v := S.units), ← sub_eq_zero,
      ← (Finsupp.total (Fin r) G A S.units).map_sub] at hg
    have := FunLike.congr_fun (linearIndependent_iff.mp S.linearIndependent _ hg) i
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same] at this
    exact one_sub_σA_mem_nonunit p σ (isUnit_of_mul_eq_one _ _ (sub_eq_zero.mp this))

lemma lemma2' [Module A G] (S : systemOfUnits p G σ r) (hs : S.IsFundamental) (i : Fin r) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) : ∀ g : G, (1 - σA p σ) • g ≠ a • (S.units i) := by
  intro g hg
  obtain ⟨x, y, e⟩ := isCoprime_one_sub_σA p σ a ha
  apply lemma2 p G σ r S hs i (x • (S.units i) + y • g)
  conv_rhs => rw [← one_smul A (S.units i), ← e, add_smul, ← smul_smul y, intCast_smul, ← hg]
  rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm x, mul_comm y]

lemma corollary [Module A G] (S : systemOfUnits p G σ r) (hs : S.IsFundamental) (a : Fin r → ℤ)
    (ha : ∃ i , ¬ (p : ℤ) ∣ a i) :
  ∀ g : G, (1 - σA p σ) • g ≠ ∑ i, a i • S.units i := sorry

end fundamentalSystemOfUnits
section application

variable
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K] [IsCyclic (K ≃ₐ[k] K)] -- technically redundant but useful
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

-- local instance : CommGroup (K ≃ₐ[k] K) where
--   mul_comm := by
--     have : Fintype.card (K ≃ₐ[k] K) = p := by
--       rwa [IsGalois.card_aut_eq_finrank]
--     have : IsCyclic (K ≃ₐ[k] K) := isCyclic_of_prime_card (hp := ⟨hp⟩) this
--     use IsCyclic.commGroup.mul_comm

local notation3 "G" => (𝓞 K)ˣ ⧸ (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : 𝓞 k →* 𝓞 K))

attribute [local instance] IsCyclic.commGroup

open CommGroup
instance : MulDistribMulAction (K ≃ₐ[k] K) (K) := inferInstance
-- instance : MulDistribMulAction (K ≃ₐ[k] K) (𝓞 K) := sorry

noncomputable
instance : MulAction (K ≃ₐ[k] K) (𝓞 K)ˣ where
  smul a := Units.map (galRestrict _ _ _ _ a : 𝓞 K ≃ₐ[ℤ] 𝓞 K)
  one_smul b := by
    change Units.map (galRestrict _ _ _ _ 1 : 𝓞 K ≃ₐ[ℤ] 𝓞 K) b = b
    rw [MonoidHom.map_one]
    rfl

  mul_smul a b c := by
    change (Units.map _) c = (Units.map _) (Units.map _ c)
    rw [MonoidHom.map_mul]
    rw [← MonoidHom.comp_apply]
    rw [← Units.map_comp]
    rfl

noncomputable
instance : MulDistribMulAction (K ≃ₐ[k] K) (𝓞 K)ˣ where
  smul_mul a b c := by
    change (Units.map _) (_ * _) = (Units.map _) _ * (Units.map _) _
    rw [MonoidHom.map_mul]
  smul_one a := by
    change (Units.map _) 1 = 1
    rw [MonoidHom.map_one]

instance : MulDistribMulAction (K ≃ₐ[k] K) G := sorry
-- instance : DistribMulAction (K ≃ₐ[k] K) (Additive G) := inferInstance
def ρ : Representation ℤ (K ≃ₐ[k] K) (Additive G) := Representation.ofMulDistribMulAction _ _
noncomputable
instance foof : Module
  (MonoidAlgebra ℤ (K ≃ₐ[k] K))
  (Additive G) := Representation.asModuleModule (ρ (k := k) (K := K))

lemma tors1 (a : Additive G) :
    (∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i) • a = 0 := by
  rw [sum_smul]
  simp only [MonoidAlgebra.of_apply]
  sorry

lemma tors2 (a : Additive G) (t)
    (ht : t ∈ Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) :
    t • a = 0 := by
  simp only [one_pow, Ideal.mem_span_singleton] at ht
  obtain ⟨r, rfl⟩ := ht
  let a': Module
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G) := foof
  let a'': MulAction
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G) := inferInstance
  rw [mul_comm, mul_smul]
  let a''': MulActionWithZero
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G) := inferInstance
  rw [tors1 p σ a, smul_zero] -- TODO this is the worst proof ever maybe because of sorries

lemma isTors : Module.IsTorsionBySet
    (MonoidAlgebra ℤ (K ≃ₐ[k] K))
    (Additive G)
    (Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i} : Set _) := by
  intro a s
  rcases s with ⟨s, hs⟩
  simp only [MonoidAlgebra.of_apply, one_pow, SetLike.mem_coe] at hs -- TODO ew why is MonoidAlgebra.single_pow simp matching here
  have := tors2 p σ a s hs
  simpa
noncomputable
local instance : Module
  (MonoidAlgebra ℤ (K ≃ₐ[k] K) ⧸
    Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) (Additive G) :=
(isTors (k := k) (K := K) p σ).module

def tors : Submodule
  (MonoidAlgebra ℤ (K ≃ₐ[k] K) ⧸
    Ideal.span {∑ i in Finset.range p, (MonoidAlgebra.of ℤ (K ≃ₐ[k] K) σ) ^ i}) (Additive G) := sorry
-- local instance : Module A (Additive G ⧸ AddCommGroup.torsion (Additive G)) := Submodule.Quotient.module _
#synth CommGroup G
#synth AddCommGroup (Additive G)
-- #check Submodule.Quotient.module (tors (k := k) (K := K) p σ)
local instance : Module A (Additive G ⧸ tors (k := k) (K := K) p σ) := by
  -- apply Submodule.Quotient.modue _
  sorry
local instance : Module.Free ℤ (Additive <| G ⧸ torsion G) := sorry
-- #exit
lemma Hilbert91ish :
    ∃ S : systemOfUnits p (Additive G ⧸ tors (k := k) (K := K) p σ) σ (NumberField.Units.rank k + 1), S.IsFundamental :=
  fundamentalSystemOfUnits.existence p (Additive G ⧸ tors (k := k) (K := K) p σ) σ (NumberField.Units.rank k + 1)
end application

end thm91

-- #exit


noncomputable

def unitlifts
  ( S : systemOfUnits p (Additive <| G ⧸ torsion G) σ (NumberField.Units.rank k + 1) )  :
  Fin (NumberField.Units.rank k + 1) → Additive (𝓞 K)ˣ := by
  let U := S.units
  intro i
  let u := (((U i)).out').out'
  exact u

lemma norm_map_inv (z : K) : Algebra.norm k z⁻¹ = (Algebra.norm k z)⁻¹ := by
    by_cases h : z = 0
    rw [h]
    simp
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel h, map_one]

lemma Hilbert92
    [Algebra k K] [IsGalois k K] [FiniteDimensional k K] [IsCyclic (K ≃ₐ[k] K)]
    (hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧ ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by

    have S := @Hilbert91ish p K _ k _ _ _ _ σ
    obtain ⟨S, _⟩ := S
    let H := @unitlifts p K _ k _ _ _ _ σ  S
    let N : Fin (NumberField.Units.rank k + 1) →  Additive (𝓞 k)ˣ :=
      fun e => Additive.ofMul (Units.map (RingOfIntegers.norm k )) (Additive.toMul (H e))
    have C := fundamentalSystemOfUnits.corollary p (Additive (𝓞 K)ˣ) σ
    have NLI : ¬ LinearIndependent ℤ N := by sorry
    rw [not_linearIndependent_iff] at NLI
    obtain ⟨t, a, ha⟩ := NLI
    by_cases T : Monoid.IsTorsionFree (𝓞 K)ˣ
    let J := Additive.toMul (∑ i in t, a i • H i)
    use J
    constructor
    let r :=   (Additive.toMul (H 1)).1

    have H1 : ∀ i : Fin (NumberField.Units.rank k + 1),
       (Algebra.norm k (( (Additive.toMul (H i)).1) : K)) = ((N i).1 : k) := by
       intro i
       simp
    have H2 : ∏ i in t, ((N i).1 : k)^ a i = 1 := sorry
    simp only [toMul_sum, toMul_zsmul, Units.coe_prod, Submonoid.coe_finset_prod,
      Subsemiring.coe_toSubmonoid, Subalgebra.coe_toSubsemiring, coe_zpow', map_prod]
    rw [←H2]
    congr
    ext1 v
    simp only [toMul_ofMul, Units.coe_map, RingOfIntegers.norm_apply_coe]
    rw [map_zpow']
    apply norm_map_inv



    sorry



end application

end thm91
