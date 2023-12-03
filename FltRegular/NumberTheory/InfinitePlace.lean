import Mathlib.NumberTheory.NumberField.Embeddings

namespace NumberField

variable {k K} [Field k] [Field K] [Algebra k K] [NumberField K]

instance : FiniteDimensional k K :=
  letI := (algebraMap k K).charZero
  Module.Finite.of_restrictScalars_finite ℚ _ _

def InfinitePlace.map (w : InfinitePlace K) (f : k →+* K) : InfinitePlace k :=
  ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; show _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

lemma InfinitePlace.map_mk (φ : K →+* ℂ) (f : k →+* K) : (mk φ).map f = mk (φ.comp f) := rfl

@[simps! smul_coe_apply]
instance : MulAction (K ≃ₐ[k] K) (InfinitePlace K) where
  smul := fun σ w ↦ w.map σ.symm
  one_smul := fun _ ↦ rfl
  mul_smul := fun _ _ _ ↦ rfl

local notation "Stab" => MulAction.stabilizer (K ≃ₐ[k] K)

@[simp]
lemma InfinitePlace.smul_apply (σ : K ≃ₐ[k] K) (w : InfinitePlace K) (x) :
    (σ • w) x = w (σ.symm x) := rfl

@[simp]
lemma InfinitePlace.smul_mk (σ : K ≃ₐ[k] K) (φ : K →+* ℂ) :
    σ • mk φ = mk (φ.comp σ.symm) := rfl

def ComplexEmbedding.IsConjGal (φ : K →+* ℂ) (σ : K ≃ₐ[k] K) : Prop :=
  ∀ x, φ (σ x) = star (φ x)

lemma ComplexEmbedding.IsConjGal.ext {φ : K →+* ℂ} {σ₁ σ₂ : K ≃ₐ[k] K}
    (h₁ : IsConjGal φ σ₁) (h₂ : IsConjGal φ σ₂) : σ₁ = σ₂ :=
  AlgEquiv.ext fun x ↦ φ.injective ((h₁ x).trans (h₂ x).symm)

lemma ComplexEmbedding.IsConjGal.ext_iff {φ : K →+* ℂ} {σ₁ σ₂ : K ≃ₐ[k] K}
    (h₁ : IsConjGal φ σ₁) : σ₁ = σ₂ ↔ IsConjGal φ σ₂ :=
  ⟨fun e ↦ e ▸ h₁, h₁.ext⟩

lemma ComplexEmbedding.isConjGal_one_iff {φ : K →+* ℂ} :
    IsConjGal φ (1 : K ≃ₐ[k] K) ↔ IsReal φ :=
  RingHom.ext_iff.symm.trans (@eq_comm _ φ (star φ))

alias ⟨_, ComplexEmbedding.IsReal.isConjGal_one⟩ := ComplexEmbedding.isConjGal_one_iff

variable (k)

def ComplexEmbedding.IsRamified (φ : K →+* ℂ) : Prop :=
    ∃ (σ : K ≃ₐ[k] K), σ ≠ 1 ∧ IsConjGal φ σ

def InfinitePlace.IsRamified (w : InfinitePlace K) : Prop :=
  Stab w ≠ ⊥

variable {k}

lemma ComplexEmbedding.IsRamified.not_isReal {φ : K →+* ℂ} (hφ : IsRamified k φ) : ¬IsReal φ :=
  fun H ↦ hφ.choose_spec.1 (H.isConjGal_one.ext hφ.choose_spec.2).symm

lemma ComplexEmbedding.IsConjGal.symm {φ : K →+* ℂ} {σ : K ≃ₐ[k] K} (hσ : IsConjGal φ σ) :
    IsConjGal φ σ.symm := fun x ↦ by simpa using congr_arg star (hσ (σ.symm x)).symm

lemma ComplexEmbedding.isConjGal_symm {φ : K →+* ℂ} {σ : K ≃ₐ[k] K} :
    IsConjGal φ σ.symm ↔ IsConjGal φ σ :=
  ⟨IsConjGal.symm, IsConjGal.symm⟩

lemma InfinitePlace.mem_stabilizer_mk_iff (φ : K →+* ℂ) (σ : K ≃ₐ[k] K) :
    σ ∈ Stab (mk φ) ↔ σ = AlgEquiv.refl ∨ ComplexEmbedding.IsConjGal φ σ := by
  simp only [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_iff]
  apply or_congr <;> constructor <;> intro H
  · exact congr_arg AlgEquiv.symm
      (AlgEquiv.ext (g := AlgEquiv.refl) fun x ↦ φ.injective (RingHom.congr_fun H x))
  · subst H; rfl
  · exact fun x ↦ by simpa using RingHom.congr_fun H.symm (σ x)
  · ext1 x; simpa using (H (σ.symm x)).symm

lemma InfinitePlace.stabilizer_mk_of_isConjGal
    {φ : K →+* ℂ} {σ : K ≃ₐ[k] K} (hσ : ComplexEmbedding.IsConjGal φ σ) :
    (Stab (mk φ) : Set (K ≃ₐ[k] K)) = {1, σ} := by
  ext x
  rw [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    ← hσ.ext_iff, @eq_comm _ σ]
  rfl

lemma InfinitePlace.stabilizer_mk_of_isReal {φ : K →+* ℂ} (hσ : ComplexEmbedding.IsReal φ) :
    Stab (mk φ) = ⊥ := Subgroup.ext fun x => by
  simpa only [Set.mem_singleton_iff, Set.insert_eq_of_mem] using
    Set.ext_iff.mp (InfinitePlace.stabilizer_mk_of_isConjGal hσ.isConjGal_one) x

lemma InfinitePlace.isReal.stabilizer_eq_bot {w : InfinitePlace K} (hσ : w.IsReal) :
    Stab w = ⊥ := by
  rw [← mk_embedding w]
  exact stabilizer_mk_of_isReal (isReal_iff.mp hσ)

lemma InfinitePlace.stabilizer_mk_of_not_isConjGal
    {φ : K →+* ℂ} (hφ : ∀ σ : K ≃ₐ[k] K, ¬ComplexEmbedding.IsConjGal φ σ) :
    Stab (mk φ) = ⊥ := by
  ext x
  simp only [mem_stabilizer_mk_iff, hφ, or_false, Subgroup.mem_bot]
  rfl

open scoped Classical

lemma InfinitePlace.stabilizer_mk_of_isRamified {φ : K →+* ℂ}
    (hφ : ComplexEmbedding.IsRamified k φ) :
    Fintype.card (Stab (mk φ)) = 2 := by
  obtain ⟨σ, hσ, hσ'⟩ := hφ
  show Fintype.card (Stab (mk φ) : Set (K ≃ₐ[k] K)) = 2
  simp [stabilizer_mk_of_isConjGal hσ', hσ.symm]

alias ComplexEmbedding.IsRamified.stabilizer_mk := InfinitePlace.stabilizer_mk_of_isRamified

lemma InfinitePlace.stabilizer_mk_of_not_isRamified {φ : K →+* ℂ}
    (hφ : ¬ ComplexEmbedding.IsRamified k φ) :
    Fintype.card (Stab (InfinitePlace.mk φ)) = 1 := by
  by_cases H : ComplexEmbedding.IsConjGal φ (1 : K ≃ₐ[k] K)
  · show Fintype.card (Stab (mk φ) : Set (K ≃ₐ[k] K)) = 1
    simp [stabilizer_mk_of_isConjGal H]
  · have : ∀ σ : K ≃ₐ[k] K, ¬ComplexEmbedding.IsConjGal φ σ :=
      fun σ hσ ↦ if e : σ = 1 then H (e ▸ hσ) else hφ ⟨σ, e, hσ⟩
    simp [stabilizer_mk_of_not_isConjGal this]

lemma ComplexEmbedding.isRamified_iff_stabilizer_mk {φ : K →+* ℂ} :
    IsRamified k φ ↔ Fintype.card (Stab (InfinitePlace.mk φ)) = 2 :=
  ⟨InfinitePlace.stabilizer_mk_of_isRamified, not_imp_not.mp <| fun H ↦
    InfinitePlace.stabilizer_mk_of_not_isRamified H ▸ Nat.ne_of_beq_eq_false rfl⟩

lemma ComplexEmbedding.not_isRamified_iff_stabilizer_mk {φ : K →+* ℂ} :
    ¬IsRamified k φ ↔ Fintype.card (Stab (InfinitePlace.mk φ)) = 1 :=
  ⟨InfinitePlace.stabilizer_mk_of_not_isRamified, not_imp_not.mp <| fun H ↦
    InfinitePlace.stabilizer_mk_of_isRamified (not_not.mp H) ▸ Nat.ne_of_beq_eq_false rfl⟩

lemma ComplexEmbedding.isRamified_iff_stabilizer_mk' {φ : K →+* ℂ} :
    IsRamified k φ ↔ Fintype.card (Stab (InfinitePlace.mk φ)) ≠ 1 :=
  (not_iff_comm.mp not_isRamified_iff_stabilizer_mk).symm

lemma ComplexEmbedding.not_isRamified_iff_stabilizer_mk' {φ : K →+* ℂ} :
    ¬IsRamified k φ ↔ Fintype.card (Stab (InfinitePlace.mk φ)) ≠ 2 :=
  not_iff_not.mpr isRamified_iff_stabilizer_mk

lemma InfinitePlace.isRamified_mk_iff {φ : K →+* ℂ} :
    IsRamified k (mk φ) ↔ ComplexEmbedding.IsRamified k φ := by
  rw [ComplexEmbedding.isRamified_iff_stabilizer_mk', IsRamified, not_iff_not,
     Subgroup.eq_bot_iff_card]

lemma InfinitePlace.card_stabilizer_mk (φ : K →+* ℂ) :
    Fintype.card (Stab (mk φ)) = if ComplexEmbedding.IsRamified k φ then 2 else 1 := by
  split
  · rwa [← ComplexEmbedding.isRamified_iff_stabilizer_mk]
  · rwa [← ComplexEmbedding.not_isRamified_iff_stabilizer_mk]

lemma InfinitePlace.card_stabilizer (w : InfinitePlace K) :
    Fintype.card (Stab w) = if w.IsRamified k then 2 else 1 := by
  rw [← mk_embedding w, card_stabilizer_mk, isRamified_mk_iff]

lemma InfinitePlace.card_stabilizer_of_isRamified {w : InfinitePlace K} (hw : w.IsRamified k) :
    Fintype.card (Stab w) = 2 := by
  rw [card_stabilizer, if_pos hw]

lemma InfinitePlace.card_stabilizer_of_not_isRamified {w : InfinitePlace K} (hw : ¬w.IsRamified k) :
    Fintype.card (Stab w) = 1 := by
  rw [card_stabilizer, if_neg hw]

open FiniteDimensional (finrank)

lemma InfinitePlace.IsRamified.even_card_aut {w : InfinitePlace K} (hw : w.IsRamified k) :
    Even (Fintype.card <| K ≃ₐ[k] K) := by
  rw [even_iff_two_dvd, ← card_stabilizer_of_isRamified hw]
  exact Subgroup.card_subgroup_dvd_card (Stab w)

lemma InfinitePlace.IsRamified.even_finrank [IsGalois k K]
    {w : InfinitePlace K} (hw : w.IsRamified k) :
    Even (finrank k K) :=
  IsGalois.card_aut_eq_finrank k K ▸ hw.even_card_aut


lemma ComplexEmbedding.exists_comp_symm_eq_of_comp_eq [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : K ≃ₐ[k] K, φ.comp σ.symm = ψ := by
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K →ₐ[k] ℂ := { ψ with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

lemma ComplexEmbedding.exists_comp_eq (h : Algebra.IsAlgebraic k K) (φ : k →+* ℂ) :
    ∃ ψ : K →+* ℂ, ψ.comp (algebraMap k K) = φ :=
  letI := φ.toAlgebra
  ⟨IsAlgClosed.lift (M := ℂ) h, AlgHom.comp_algebraMap _⟩

lemma InfinitePlace.exists_smul_eq_of_map_eq [IsGalois k K] (w w' : InfinitePlace K)
    (h : w.map (algebraMap k K) = w'.map (algebraMap k K)) : ∃ σ : K ≃ₐ[k] K, σ • w = w' := by
  rw [← mk_embedding w, ← mk_embedding w', map_mk, map_mk, mk_eq_iff] at h
  cases h with
  | inl h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, hσ]
  | inr h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      ((starRingEnd ℂ).comp (embedding w)) w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, mk_eq_iff]
    exact Or.inr hσ

lemma InfinitePlace.mem_orbit_iff [IsGalois k K] {w w' : InfinitePlace K} :
    w' ∈ MulAction.orbit (K ≃ₐ[k] K) w ↔ w.map (algebraMap k K) = w'.map (algebraMap k K) := by
  refine ⟨?_, InfinitePlace.exists_smul_eq_of_map_eq w w'⟩
  rintro ⟨σ, rfl : σ • w = w'⟩
  rw [← mk_embedding w, map_mk, smul_mk, map_mk]
  congr 1; ext1; simp

lemma InfinitePlace.map_surjective (h : Algebra.IsAlgebraic k K) :
    Function.Surjective (map · (algebraMap k K)) := fun w ↦
  have ⟨ψ, hψ⟩ := ComplexEmbedding.exists_comp_eq h w.embedding
  ⟨mk ψ, by simp [map_mk, hψ]⟩

noncomputable
def InfinitePlace.orbitRelEquiv [IsGalois k K] :
    Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (InfinitePlace K)) ≃ InfinitePlace k := by
  refine Equiv.ofBijective (Quotient.lift (map · (algebraMap k K))
    <| fun _ _ e ↦ (mem_orbit_iff.mp e).symm) ⟨?_, ?_⟩
  · rintro ⟨w⟩ ⟨w'⟩ e
    exact Quotient.sound (mem_orbit_iff.mpr e.symm)
  · intro w
    obtain ⟨w', hw⟩ := map_surjective (Normal.isAlgebraic' (K := K)) w
    exact ⟨⟦w'⟧, hw⟩

lemma InfinitePlace.orbitRelEquiv_apply_mk'' [IsGalois k K] (x : InfinitePlace K) :
    orbitRelEquiv (Quotient.mk'' x) = map x (algebraMap k K) := rfl

lemma InfinitePlace.isRamified_smul {σ : K ≃ₐ[k] K} {w : InfinitePlace K} :
    IsRamified k (σ • w) ↔ IsRamified k w := by
  rw [IsRamified, IsRamified, MulAction.stabilizer_smul_eq_stabilizer_map_conj, not_iff_not,
    Subgroup.eq_bot_iff_card, Subgroup.eq_bot_iff_card, iff_iff_eq]
  congr 1
  exact Fintype.card_congr ((MulAut.conj σ).subgroupMap _).symm.toEquiv

variable (K)

def InfinitePlace.IsRamifiedIn [IsGalois k K] (w : InfinitePlace k) : Prop :=
  ((map_surjective (Normal.isAlgebraic' (K := K))) w).choose.IsRamified k

variable {K}

lemma InfinitePlace.isRamifiedIn_map [IsGalois k K] {w : InfinitePlace K} :
    (w.map (algebraMap k K)).IsRamifiedIn K ↔ w.IsRamified k := by
  let w' := (map_surjective (Normal.isAlgebraic' (K := K)) (w.map (algebraMap k K))).choose
  have hw : w'.map (algebraMap k K) = w.map (algebraMap k K) :=
    (map_surjective (Normal.isAlgebraic' (K := K)) (w.map (algebraMap k K))).choose_spec
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_map_eq _ _ hw.symm
  show w'.IsRamified k ↔ w.IsRamified k
  rw [← hσ, InfinitePlace.isRamified_smul]

nonrec lemma InfinitePlace.IsRamifiedIn.even_card_aut
    [IsGalois k K] {w : InfinitePlace k} (hw : w.IsRamifiedIn K) :
    Even (Fintype.card <| K ≃ₐ[k] K) :=
  hw.even_card_aut

nonrec lemma InfinitePlace.IsRamifiedIn.even_finrank
    [IsGalois k K] {w : InfinitePlace k} (hw : w.IsRamifiedIn K) :
    Even (finrank k K) :=
  hw.even_finrank

open Finset BigOperators in
lemma InfinitePlace.card_isRamified [NumberField k] [IsGalois k K] :
    card (univ.filter <| IsRamified k (K := K)) =
      card (univ.filter <| IsRamifiedIn K (k := k)) * (finrank k K / 2) := by
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (map · (algebraMap k K)))
    (t := (univ.filter <| IsRamifiedIn K (k := k))), ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl (fun w hw ↦ ?_)
  obtain ⟨w, rfl⟩ := map_surjective (Normal.isAlgebraic' (K := K)) w
  simp only [mem_univ, forall_true_left, mem_filter, true_and] at hw
  trans card (MulAction.orbit (K ≃ₐ[k] K) w).toFinset
  · congr; ext w'
    simp only [mem_univ, forall_true_left, filter_congr_decidable, mem_filter, true_and,
      Set.mem_toFinset, mem_orbit_iff, @eq_comm _ (map w' _), and_iff_right_iff_imp]
    intro e; rwa [← isRamifiedIn_map, ← e]
  · rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
      InfinitePlace.card_stabilizer, if_pos, Nat.mul_div_cancel _ zero_lt_two, Set.toFinset_card]
    rwa [← isRamifiedIn_map]
  · simp [isRamifiedIn_map]

open Finset BigOperators in
lemma InfinitePlace.card_isRamified_compl [NumberField k] [IsGalois k K] :
    card (univ.filter <| IsRamified k (K := K))ᶜ =
      card (univ.filter <| IsRamifiedIn K (k := k))ᶜ * finrank k K := by
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (map · (algebraMap k K)))
    (t := (univ.filter <| IsRamifiedIn K (k := k))ᶜ), ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl (fun w hw ↦ ?_)
  obtain ⟨w, rfl⟩ := map_surjective (Normal.isAlgebraic' (K := K)) w
  simp only [mem_univ, forall_true_left, compl_filter, not_not, mem_filter, true_and] at hw
  trans card (MulAction.orbit (K ≃ₐ[k] K) w).toFinset
  · congr; ext w'
    simp only [compl_filter, filter_congr_decidable, mem_filter, mem_univ, true_and,
      @eq_comm _ (map w' _), Set.mem_toFinset, mem_orbit_iff, and_iff_right_iff_imp]
    intro e; rwa [← isRamifiedIn_map, ← e]
  · rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
      InfinitePlace.card_stabilizer, if_neg, mul_one, Set.toFinset_card]
    rwa [← isRamifiedIn_map]
  · simp [isRamifiedIn_map]

open Finset in
lemma InfinitePlace.card_eq [NumberField k] [IsGalois k K] :
    Fintype.card (InfinitePlace K) =
      card (univ.filter <| IsRamifiedIn K (k := k)) * (finrank k K / 2) +
      card (univ.filter <| IsRamifiedIn K (k := k))ᶜ * finrank k K := by
  rw [← card_isRamified, ← card_isRamified_compl, card_add_card_compl]

open Finset in
lemma InfinitePlace.card_eq_card_isRamifiedIn [NumberField k] [IsGalois k K] :
    Fintype.card (InfinitePlace K) =
      Fintype.card (InfinitePlace k) * finrank k K -
      card (univ.filter <| IsRamifiedIn K (k := k)) * (finrank k K / 2) := by
  apply eq_tsub_of_add_eq
  rw [card_eq (k := k), add_comm, ← add_assoc, ← mul_add, ← mul_two,
    ← card_add_card_compl (univ.filter <| IsRamifiedIn K (k := k)), add_mul]
  congr 1
  by_cases H : card (univ.filter <| IsRamifiedIn K (k := k)) = 0
  · rw [H, zero_mul, zero_mul]
  · simp only [mem_univ, forall_true_left, card_eq_zero,
      filter_eq_empty_iff, not_forall, not_not] at H
    rw [Nat.div_mul_cancel H.choose_spec.even_finrank.two_dvd]

class InfinitePlace.IsUnramified (k K) [Field k] [Field K] [Algebra k K] : Prop where
  not_isRamified : ∀ w : InfinitePlace K, ¬ IsRamified k w

lemma InfinitePlace.not_isRamified (k) {K} [Field k] [Field K] [Algebra k K] [IsUnramified k K]
    (w : InfinitePlace K) : ¬ IsRamified k w := IsUnramified.not_isRamified w

lemma InfinitePlace.not_isRamifiedIn {k} (K) [Field k] [Field K] [Algebra k K] [IsUnramified k K]
  [IsGalois k K] (w : InfinitePlace k) : ¬ w.IsRamifiedIn K := IsUnramified.not_isRamified _

lemma InfinitePlace.isUnramified_of_odd_card_aut (h : Odd (Fintype.card <| K ≃ₐ[k] K)) :
    IsUnramified k K where
  not_isRamified _ hw := Nat.odd_iff_not_even.mp h hw.even_card_aut

lemma InfinitePlace.isUramified_of_odd_finrank [IsGalois k K] (h : Odd (finrank k K)) :
    IsUnramified k K where
  not_isRamified _ hw := Nat.odd_iff_not_even.mp h hw.even_finrank

lemma InfinitePlace.card_eq_of_isUnramified [NumberField k] [IsGalois k K]
    [IsUnramified k K] :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace k) * finrank k K := by
  rw [card_eq_card_isRamifiedIn (k := k) (K := K), Finset.card_eq_zero.mpr, zero_mul, tsub_zero]
  simp only [Finset.mem_univ, forall_true_left, Finset.filter_eq_empty_iff]
  exact InfinitePlace.not_isRamifiedIn K

end NumberField
