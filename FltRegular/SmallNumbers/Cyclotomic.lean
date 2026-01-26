module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import FltRegular.SmallNumbers.PID
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

@[expose] public section

lemma uff {n p : ℕ} [hp : Fact p.Prime] (hn : n.Prime) (hpn : p ≠ n) : p.Coprime n :=
  hp.1.coprime_iff_not_dvd.mpr (fun h ↦ hpn <|
    Nat.prime_eq_prime_of_dvd_pow hp.1 hn (m := 1) (by simpa))

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid Ideal

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace IsCyclotomicExtension.Rat

local notation3 "θ" => (zeta_spec n ℚ K).toInteger

variable (n K) in
lemma minpoly : minpoly ℤ θ = cyclotomic n ℤ := by
  have := cyclotomic_eq_minpoly (zeta_spec n ℚ K) (NeZero.pos n)
  rw [← (zeta_spec n ℚ K).coe_toInteger] at this
  simpa [this] using (minpoly.algebraMap_eq RingOfIntegers.coe_injective θ).symm

variable (n) in
lemma exponent : exponent θ = 1 := by
  simp [exponent_eq_one_iff, ← ((zeta_spec n ℚ K).integralPowerBasis).adjoin_gen_eq_top]

lemma ne_dvd_exponent (p : ℕ) [hp : Fact p.Prime] : ¬ (p ∣ RingOfIntegers.exponent θ) := by
  rw [exponent, dvd_one]
  exact hp.1.ne_one

variable (n)

theorem pid1 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → p ≠ n →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P, ∃ hP : P ∈ monicFactorsMod θ p, ⌊(M K)⌋₊ < p ^ P.natDegree ∨
        Submodule.IsPrincipal ((primesOverSpanEquivMonicFactorsMod (ne_dvd_exponent p)).symm
          ⟨P, hP⟩).1) : IsPrincipalIdealRing (𝓞 K) := by
  have : IsGalois ℚ K := isGalois {n} ℚ K
  refine PIDGalois (exponent n) (fun p hple hp ↦ ?_)
  have : Fact (p.Prime) := ⟨hp⟩
  by_cases hpn : p = n
  · let Q : ℤ[X] := X - 1
    have hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p := by
      simp only [Polynomial.map_sub, map_X, Polynomial.map_one, mem_toFinset, Q]
      refine (Polynomial.mem_normalizedFactors_iff ((Monic.map _ <|
        minpoly n K ▸ monic ↑n ℤ).ne_zero)).mpr ⟨irreducible_of_degree_eq_one (by compute_degree!),
        by monicity, ⟨(X - 1) ^ (p - 2), ?_⟩⟩
      simp only [minpoly n K, map_cyclotomic]
      rw [← mul_one n, ←pow_one (n : ℕ), ← hpn, cyclotomic_mul_prime_pow_eq (ZMod p) hp.not_dvd_one
        one_pos]
      simp only [cyclotomic_one, pow_one, tsub_self, pow_zero]
      rw [← pow_succ' (X - 1)]
      congr
      have := hp.two_le
      omega
    refine ⟨Q.map (Int.castRingHom (ZMod p)), hQ, ?_⟩
    right
    rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (ne_dvd_exponent p) hQ]
    simp only [map_sub, aeval_X, map_one, Q]
    refine ⟨θ - 1, le_antisymm (span_le.mpr <| fun x hx ↦ ?_) (span_le.mpr ?_)⟩
    · rcases hx with rfl | rfl
      · subst hpn
        simp [mem_span_singleton, (zeta_spec _ ℚ K).toInteger_sub_one_dvd_prime']
      · exact subset_span (by simp)
    · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      exact subset_span (by simp)
  · exact h p hple hp hpn

theorem pid2 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → p ≠ n →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P : ℤ[X], P.Monic ∧ P.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p ∧
        (⌊(M K)⌋₊ < p ^ P.natDegree ∨
          Submodule.IsPrincipal (span {↑p, aeval θ P}))) : IsPrincipalIdealRing (𝓞 K) := by
    refine pid1 n (fun p hple hp hpn ↦ ?_)
    have : Fact (p.Prime) := ⟨hp⟩
    obtain ⟨P, hPmo, hP, hM⟩ := h p hple hp hpn
    refine ⟨P.map (Int.castRingHom (ZMod p)), hP, ?_⟩
    rcases hM with H | H
    · left
      convert H
      simp [hPmo.leadingCoeff]
    · right
      simpa [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (ne_dvd_exponent p) hP]

variable [hn : Fact (Nat.Prime n)]

theorem pid3 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → (hpn : p ≠ n) →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P Q A : ℤ[X], P.Monic ∧ orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) = P.natDegree
      ∧ P * Q + p * A = cyclotomic n ℤ ∧
        (⌊(M K)⌋₊ < p ^ P.natDegree ∨
          Submodule.IsPrincipal (span {↑p, aeval θ P}))) : IsPrincipalIdealRing (𝓞 K) := by
  refine pid2 n (fun p hple hp hpn ↦ ?_)
  have : Fact (p.Prime) := ⟨hp⟩
  obtain ⟨P, Q, A, hPmo, hP, hQA, hM⟩ := h p hple hp hpn
  have : P.map (Int.castRingHom (ZMod p)) ∣ cyclotomic n (ZMod p) := by
    refine ⟨Q.map (Int.castRingHom (ZMod p)), ?_⟩
    simp [← map_cyclotomic n (Int.castRingHom (ZMod p)), ← hQA]
  refine ⟨P, hPmo, mem_toFinset.mpr <| (Polynomial.mem_normalizedFactors_iff
    (((minpoly.monic (isIntegral θ)).map _).ne_zero)).mpr ⟨?_, hPmo.map _,
    by simp [minpoly, ← hQA]⟩, hM⟩
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (fun h ↦ ?_) this (by simp [← hP, hPmo])
  exact hp.ne_one <| ((Nat.dvd_prime hn.1).1 h).resolve_right hpn

theorem pid4 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → (hpn : p ≠ n) →
    haveI : Fact (p.Prime) := ⟨hp⟩
      ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
        P.Monic ∧ orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) = P.natDegree
          ∧ P * Q + p * A = cyclotomic n ℤ ∧
            (⌊(M K)⌋₊ < p ^ P.natDegree ∨
              (p = G * Qp + Rp * (cyclotomic n ℤ) ∧ P = G * QP + RP * (cyclotomic n ℤ) ∧
               G = C1 * P + C2 * p ))) : IsPrincipalIdealRing (𝓞 K) := by
  refine pid3 n (fun p hple hp hpn ↦ ?_)
  obtain ⟨P, Q, A, G, Qp, Rp, QP, RP, C1, C2, hPmo, hP, hQA, hM⟩ := h p hple hp hpn
  refine ⟨P, Q, A, hPmo, hP, hQA, ?_⟩
  rcases hM with H | ⟨Hp, HP, HG⟩
  · left
    assumption
  · right
    refine ⟨aeval θ G, le_antisymm (span_le.mpr <| fun x hx ↦ ?_) (span_le.mpr ?_)⟩
    · rcases hx with rfl | rfl
      · simp only [submodule_span_eq, SetLike.mem_coe, mem_span_singleton]
        refine ⟨aeval θ Qp, ?_⟩
        rw [← aeval_mul, ← sub_eq_iff_eq_add.mpr Hp]
        simp [← minpoly n K]
      · simp only [submodule_span_eq, SetLike.mem_coe, mem_span_singleton]
        refine ⟨aeval θ QP, ?_⟩
        rw [← aeval_mul, ← sub_eq_iff_eq_add.mpr HP]
        simp [← minpoly n K]
    · simp only [Set.singleton_subset_iff, SetLike.mem_coe, HG, _root_.map_add, map_mul,
        map_natCast]
      exact add_mem (mul_mem_left _ _ (subset_span (by simp)))
        (mul_mem_left _ _ (subset_span (by simp)))

theorem pid5 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → (hpn : p ≠ n) →
    haveI : Fact (p.Prime) := ⟨hp⟩
    ⌊(M K)⌋₊ < p ^ orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) ∨
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) = P.natDegree
        ∧ P * Q + p * A = cyclotomic n ℤ ∧ (p = G * Qp + Rp * (cyclotomic n ℤ) ∧
          P = G * QP + RP * (cyclotomic n ℤ) ∧ G = C1 * P + C2 * p)) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine pid4 n (fun p hple hp hpn ↦ ?_)
  have : Fact (p.Prime) := ⟨hp⟩
  rcases h p hple hp hpn with H | H
  · obtain ⟨P', hP'⟩ := exists_mem_normalizedFactors (cyclotomic_ne_zero n (ZMod p))
      (not_isUnit_of_degree_pos _ <| degree_cyclotomic_pos _ _ (NeZero.pos n))
    obtain ⟨hP'irr, hP'mo, Q', hQ'⟩ :=
      (Polynomial.mem_normalizedFactors_iff (cyclotomic_ne_zero n (ZMod p))).mp hP'
    obtain ⟨P, hP, hPdeg, hPmo⟩ := lifts_and_degree_eq_and_monic ((mem_lifts P').mpr
      (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p))) _)) hP'mo
    obtain ⟨Q, hQ⟩ := ((mem_lifts Q').mp (map_surjective _
      (ZMod.ringHom_surjective (Int.castRingHom (ZMod p))) _))
    set A' := cyclotomic n ℤ - P * Q with hA'def
    obtain ⟨A, hA⟩ : ↑p ∣ A' := by
      rw [← C_eq_natCast, C_dvd_iff_dvd_coeff]
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hA'def, coeff_sub, Int.cast_sub,
        ← eq_intCast (Int.castRingHom _), ← eq_intCast (Int.castRingHom _), ← coeff_map,
        ← coeff_map, ← coeff_sub, Polynomial.map_mul, map_cyclotomic, hP, hQ, hQ']
      simp
    have H : orderOf (ZMod.unitOfCoprime p (uff hn.1 hpn)) = P.natDegree := by
      rw [natDegree_eq_of_degree_eq hPdeg]
      convert (natDegree_of_dvd_cyclotomic_of_irreducible (f := 1) (p := p) (by simp)
        (by simpa using uff hn.1 hpn) ⟨Q', hQ'⟩ hP'irr).symm
      simp
    refine ⟨P, Q, A, 0, 0, 0, 0, 0, 0, 0, hPmo, H, by simp [← hA, A'], ?_⟩
    · left
      rwa [← H]
  · obtain ⟨P, Q, A, G, Qp, Rp, QP, RP, C1, C2, hPmo, hP, hQA, hG, H1, H2⟩ := H
    exact ⟨P, Q, A, G, Qp, Rp, QP, RP, C1, C2, hPmo, hP, hQA, Or.inr ⟨hG, H1, H2⟩⟩

open nonZeroDivisors in
theorem pid6 (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, (hp : p.Prime) → (hpn : p ≠ n) →
    haveI : Fact (p.Prime) := ⟨hp⟩
    Nat.log p ⌊(M K)⌋₊ < orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) ∨
    ∃ P Q A G Qp Rp QP RP C1 C2 : ℤ[X],
      P.Monic ∧ orderOf (ZMod.unitOfCoprime _ (uff hn.1 hpn)) = P.natDegree
        ∧ P * Q + p * A = cyclotomic n ℤ ∧ (p = G * Qp + Rp * (cyclotomic n ℤ) ∧
          P = G * QP + RP * (cyclotomic n ℤ) ∧ G = C1 * P + C2 * p)) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine pid5 n (fun p hple hp hpn ↦ ?_)
  rcases h p hple hp hpn with H | H
  · left
    refine (Nat.log_lt_iff_lt_pow hp.one_lt ?_).mp H
    simp only [ne_eq, floor_eq_zero, not_lt]
    obtain ⟨I, -, hI⟩ := exists_ideal_in_class_of_norm_le (1 : ClassGroup (𝓞 K))
    exact le_trans (one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr
      (absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr I.2))) hI
  · right
    exact H

end IsCyclotomicExtension.Rat
