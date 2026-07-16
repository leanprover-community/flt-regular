import BealRegular.SeventeenBounds
import BealRegular.SeventeenCertificates00
import BealRegular.SeventeenCertificates01
import BealRegular.SeventeenCertificates02
import BealRegular.SeventeenCertificates03
import BealRegular.SeventeenCertificates04
import BealRegular.SeventeenCertificates05
import BealRegular.SeventeenCertificates06
import BealRegular.SeventeenCertificates07
import BealRegular.SeventeenCertificates08
import BealRegular.SeventeenCertificates09
import BealRegular.SeventeenCertificates10

/-!
# The regular prime 17

The 103 exact polynomial certificates imported above prove that the ring of
integers of the seventeenth cyclotomic field is a PID. Sage discovered the witnesses; Lean's
kernel checks every displayed polynomial identity and finite order calculation.
-/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {17} ℚ K]

set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
variable (K) in
theorem Rat.seventeen_pid : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 17
  rw [M17]
  intro p hple hp hpn
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hmem : p ∈ exceptionalPrimesSeventeen
  · simp only [exceptionalPrimesSeventeen, List.mem_toFinset, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · right
      exact seventeenCertificate_2 hpn
    · right
      exact seventeenCertificate_67 hpn
    · right
      exact seventeenCertificate_101 hpn
    · right
      exact seventeenCertificate_103 hpn (by norm_num)
    · right
      exact seventeenCertificate_137 hpn (by norm_num)
    · right
      exact seventeenCertificate_239 hpn (by norm_num)
    · right
      exact seventeenCertificate_307 hpn (by norm_num)
    · right
      exact seventeenCertificate_409 hpn (by norm_num)
    · right
      exact seventeenCertificate_443 hpn (by norm_num)
    · right
      exact seventeenCertificate_613 hpn (by norm_num)
    · right
      exact seventeenCertificate_647 hpn (by norm_num)
    · right
      exact seventeenCertificate_919 hpn (by norm_num)
    · right
      exact seventeenCertificate_953 hpn (by norm_num)
    · right
      exact seventeenCertificate_1021 hpn (by norm_num)
    · right
      exact seventeenCertificate_1123 hpn (by norm_num)
    · right
      exact seventeenCertificate_1259 hpn (by norm_num)
    · right
      exact seventeenCertificate_1327 hpn (by norm_num)
    · right
      exact seventeenCertificate_1361 hpn (by norm_num)
    · right
      exact seventeenCertificate_1429 hpn (by norm_num)
    · right
      exact seventeenCertificate_1531 hpn (by norm_num)
    · right
      exact seventeenCertificate_1667 hpn (by norm_num)
    · right
      exact seventeenCertificate_1871 hpn (by norm_num)
    · right
      exact seventeenCertificate_1973 hpn (by norm_num)
    · right
      exact seventeenCertificate_2143 hpn (by norm_num)
    · right
      exact seventeenCertificate_2347 hpn (by norm_num)
    · right
      exact seventeenCertificate_2381 hpn (by norm_num)
    · right
      exact seventeenCertificate_2551 hpn (by norm_num)
    · right
      exact seventeenCertificate_2687 hpn (by norm_num)
    · right
      exact seventeenCertificate_2789 hpn (by norm_num)
    · right
      exact seventeenCertificate_2857 hpn (by norm_num)
    · right
      exact seventeenCertificate_3061 hpn (by norm_num)
    · right
      exact seventeenCertificate_3163 hpn (by norm_num)
    · right
      exact seventeenCertificate_3299 hpn (by norm_num)
    · right
      exact seventeenCertificate_3469 hpn (by norm_num)
    · right
      exact seventeenCertificate_3571 hpn (by norm_num)
    · right
      exact seventeenCertificate_3673 hpn (by norm_num)
    · right
      exact seventeenCertificate_3877 hpn (by norm_num)
    · right
      exact seventeenCertificate_3911 hpn (by norm_num)
    · right
      exact seventeenCertificate_4013 hpn (by norm_num)
    · right
      exact seventeenCertificate_4217 hpn (by norm_num)
    · right
      exact seventeenCertificate_4421 hpn (by norm_num)
    · right
      exact seventeenCertificate_4523 hpn (by norm_num)
    · right
      exact seventeenCertificate_4591 hpn (by norm_num)
    · right
      exact seventeenCertificate_4931 hpn (by norm_num)
    · right
      exact seventeenCertificate_4999 hpn (by norm_num)
    · right
      exact seventeenCertificate_5101 hpn (by norm_num)
    · right
      exact seventeenCertificate_5237 hpn (by norm_num)
    · right
      exact seventeenCertificate_5407 hpn (by norm_num)
    · right
      exact seventeenCertificate_5441 hpn (by norm_num)
    · right
      exact seventeenCertificate_5849 hpn (by norm_num)
    · right
      exact seventeenCertificate_6053 hpn (by norm_num)
    · right
      exact seventeenCertificate_6121 hpn (by norm_num)
    · right
      exact seventeenCertificate_6257 hpn (by norm_num)
    · right
      exact seventeenCertificate_6359 hpn (by norm_num)
    · right
      exact seventeenCertificate_6427 hpn (by norm_num)
    · right
      exact seventeenCertificate_6529 hpn (by norm_num)
    · right
      exact seventeenCertificate_6563 hpn (by norm_num)
    · right
      exact seventeenCertificate_6733 hpn (by norm_num)
    · right
      exact seventeenCertificate_6869 hpn (by norm_num)
    · right
      exact seventeenCertificate_6971 hpn (by norm_num)
    · right
      exact seventeenCertificate_7039 hpn (by norm_num)
    · right
      exact seventeenCertificate_7243 hpn (by norm_num)
    · right
      exact seventeenCertificate_7481 hpn (by norm_num)
    · right
      exact seventeenCertificate_7549 hpn (by norm_num)
    · right
      exact seventeenCertificate_7583 hpn (by norm_num)
    · right
      exact seventeenCertificate_7753 hpn (by norm_num)
    · right
      exact seventeenCertificate_8059 hpn (by norm_num)
    · right
      exact seventeenCertificate_8093 hpn (by norm_num)
    · right
      exact seventeenCertificate_8161 hpn (by norm_num)
    · right
      exact seventeenCertificate_8263 hpn (by norm_num)
    · right
      exact seventeenCertificate_8297 hpn (by norm_num)
    · right
      exact seventeenCertificate_8467 hpn (by norm_num)
    · right
      exact seventeenCertificate_8501 hpn (by norm_num)
    · right
      exact seventeenCertificate_8807 hpn (by norm_num)
    · right
      exact seventeenCertificate_9011 hpn (by norm_num)
    · right
      exact seventeenCertificate_9181 hpn (by norm_num)
    · right
      exact seventeenCertificate_9283 hpn (by norm_num)
    · right
      exact seventeenCertificate_9419 hpn (by norm_num)
    · right
      exact seventeenCertificate_9521 hpn (by norm_num)
    · right
      exact seventeenCertificate_9623 hpn (by norm_num)
    · right
      exact seventeenCertificate_9929 hpn (by norm_num)
    · right
      exact seventeenCertificate_10099 hpn (by norm_num)
    · right
      exact seventeenCertificate_10133 hpn (by norm_num)
    · right
      exact seventeenCertificate_10303 hpn (by norm_num)
    · right
      exact seventeenCertificate_10337 hpn (by norm_num)
    · right
      exact seventeenCertificate_10711 hpn (by norm_num)
    · right
      exact seventeenCertificate_10847 hpn (by norm_num)
    · right
      exact seventeenCertificate_10949 hpn (by norm_num)
    · right
      exact seventeenCertificate_11119 hpn (by norm_num)
    · right
      exact seventeenCertificate_11527 hpn (by norm_num)
    · right
      exact seventeenCertificate_11731 hpn (by norm_num)
    · right
      exact seventeenCertificate_11833 hpn (by norm_num)
    · right
      exact seventeenCertificate_11867 hpn (by norm_num)
    · right
      exact seventeenCertificate_11969 hpn (by norm_num)
    · right
      exact seventeenCertificate_12037 hpn (by norm_num)
    · right
      exact seventeenCertificate_12071 hpn (by norm_num)
    · right
      exact seventeenCertificate_12241 hpn (by norm_num)
    · right
      exact seventeenCertificate_12343 hpn (by norm_num)
    · right
      exact seventeenCertificate_12377 hpn (by norm_num)
    · right
      exact seventeenCertificate_12479 hpn (by norm_num)
    · right
      exact seventeenCertificate_12547 hpn (by norm_num)
    · right
      exact seventeenCertificate_12853 hpn (by norm_num)
    · right
      exact seventeenCertificate_13159 hpn (by norm_num)
  · left
    exact log_lt_orderOf_seventeen_of_not_mem hp hpn (Finset.mem_Icc.mp hple).2 hmem

set_option backward.isDefEq.respectTransparency false in
theorem isRegularPrime_seventeen :
    haveI : Fact (Nat.Prime 17) := ⟨Nat.prime_seventeen⟩
    IsRegularPrime 17 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.seventeen_pid (CyclotomicField _ ℚ))

theorem fermatLastTheoremSeventeen : FermatLastTheoremFor 17 :=
  @flt_regular 17 ⟨Nat.prime_seventeen⟩ isRegularPrime_seventeen (by omega)
