import BealRegular.NineteenBounds
import BealRegular.NineteenCertificates00
import BealRegular.NineteenCertificates01
import BealRegular.NineteenCertificates02
import BealRegular.NineteenCertificates03
import BealRegular.NineteenCertificates04
import BealRegular.NineteenCertificates05
import BealRegular.NineteenCertificates06
import BealRegular.NineteenCertificates07
import BealRegular.NineteenCertificates08
import BealRegular.NineteenCertificates09
import BealRegular.NineteenCertificates10
import BealRegular.NineteenCertificates11

/-!
# The regular prime 19

The 558 exact polynomial certificates imported above prove that the ring of
integers of the nineteenth cyclotomic field is a PID. Sage discovered the witnesses; Lean's
kernel checks every displayed polynomial identity and finite order calculation.
-/

@[expose] public section

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {19} ℚ K]

set_option linter.flexible false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.style.longLine false in
set_option maxHeartbeats 0 in
-- Dispatches all 558 independently checked exceptional-prime certificates.
set_option maxRecDepth 30000 in
variable (K) in
theorem Rat.nineteen_pid : IsPrincipalIdealRing (𝓞 K) := by
  apply IsCyclotomicExtension.Rat.pid6 19
  rw [M19]
  intro p hple hp hpn
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hmod : p % 19 = 1
  · have hmem := prime_mem_exceptionalSplitPrimesNineteen_of_mod_eq_one hp
      (Finset.mem_Icc.mp hple).2 hmod
    simp only [exceptionalSplitPrimesNineteen, Finset.mem_union] at hmem
    rcases hmem with hlocal00 | hlocal01 | hlocal02 | hlocal03 | hlocal04 | hlocal05 | hlocal06 | hlocal07 | hlocal08 | hlocal09 | hlocal10 | hlocal11 | hlocal12 | hlocal13 | hlocal14 | hlocal15 | hlocal16 | hlocal17 | hlocal18 | hlocal19 | hlocal20 | hlocal21 | hlocal22
    · simp only [exceptionalSplitPrimesNineteen_00, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal00
      rcases hlocal00 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_191 hpn hmod
      · right
        exact nineteenCertificate_229 hpn hmod
      · right
        exact nineteenCertificate_419 hpn hmod
      · right
        exact nineteenCertificate_457 hpn hmod
      · right
        exact nineteenCertificate_571 hpn hmod
      · right
        exact nineteenCertificate_647 hpn hmod
      · right
        exact nineteenCertificate_761 hpn hmod
      · right
        exact nineteenCertificate_1103 hpn hmod
      · right
        exact nineteenCertificate_1217 hpn hmod
      · right
        exact nineteenCertificate_1483 hpn hmod
      · right
        exact nineteenCertificate_1559 hpn hmod
      · right
        exact nineteenCertificate_1597 hpn hmod
      · right
        exact nineteenCertificate_1787 hpn hmod
      · right
        exact nineteenCertificate_1901 hpn hmod
      · right
        exact nineteenCertificate_2053 hpn hmod
      · right
        exact nineteenCertificate_2129 hpn hmod
      · right
        exact nineteenCertificate_2243 hpn hmod
      · right
        exact nineteenCertificate_2281 hpn hmod
      · right
        exact nineteenCertificate_2357 hpn hmod
      · right
        exact nineteenCertificate_2699 hpn hmod
      · right
        exact nineteenCertificate_2851 hpn hmod
      · right
        exact nineteenCertificate_2927 hpn hmod
      · right
        exact nineteenCertificate_3041 hpn hmod
      · right
        exact nineteenCertificate_3079 hpn hmod
      · right
        exact nineteenCertificate_3307 hpn hmod
      · right
        exact nineteenCertificate_3877 hpn hmod
      · right
        exact nineteenCertificate_4219 hpn hmod
      · right
        exact nineteenCertificate_4409 hpn hmod
      · right
        exact nineteenCertificate_4447 hpn hmod
      · right
        exact nineteenCertificate_4523 hpn hmod
      · right
        exact nineteenCertificate_4561 hpn hmod
      · right
        exact nineteenCertificate_4637 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_01, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal01
      rcases hlocal01 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_4751 hpn hmod
      · right
        exact nineteenCertificate_4789 hpn hmod
      · right
        exact nineteenCertificate_4903 hpn hmod
      · right
        exact nineteenCertificate_5701 hpn hmod
      · right
        exact nineteenCertificate_6043 hpn hmod
      · right
        exact nineteenCertificate_6271 hpn hmod
      · right
        exact nineteenCertificate_6689 hpn hmod
      · right
        exact nineteenCertificate_6803 hpn hmod
      · right
        exact nineteenCertificate_6841 hpn hmod
      · right
        exact nineteenCertificate_6917 hpn hmod
      · right
        exact nineteenCertificate_7069 hpn hmod
      · right
        exact nineteenCertificate_7297 hpn hmod
      · right
        exact nineteenCertificate_7411 hpn hmod
      · right
        exact nineteenCertificate_7487 hpn hmod
      · right
        exact nineteenCertificate_7639 hpn hmod
      · right
        exact nineteenCertificate_7753 hpn hmod
      · right
        exact nineteenCertificate_7829 hpn hmod
      · right
        exact nineteenCertificate_7867 hpn hmod
      · right
        exact nineteenCertificate_8171 hpn hmod
      · right
        exact nineteenCertificate_8209 hpn hmod
      · right
        exact nineteenCertificate_8513 hpn hmod
      · right
        exact nineteenCertificate_8627 hpn hmod
      · right
        exact nineteenCertificate_8741 hpn hmod
      · right
        exact nineteenCertificate_8779 hpn hmod
      · right
        exact nineteenCertificate_8893 hpn hmod
      · right
        exact nineteenCertificate_8969 hpn hmod
      · right
        exact nineteenCertificate_9007 hpn hmod
      · right
        exact nineteenCertificate_9311 hpn hmod
      · right
        exact nineteenCertificate_9349 hpn hmod
      · right
        exact nineteenCertificate_9463 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_02, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal02
      rcases hlocal02 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_9539 hpn hmod
      · right
        exact nineteenCertificate_9767 hpn hmod
      · right
        exact nineteenCertificate_10223 hpn hmod
      · right
        exact nineteenCertificate_10337 hpn hmod
      · right
        exact nineteenCertificate_10831 hpn hmod
      · right
        exact nineteenCertificate_11059 hpn hmod
      · right
        exact nineteenCertificate_11173 hpn hmod
      · right
        exact nineteenCertificate_11287 hpn hmod
      · right
        exact nineteenCertificate_11743 hpn hmod
      · right
        exact nineteenCertificate_11933 hpn hmod
      · right
        exact nineteenCertificate_11971 hpn hmod
      · right
        exact nineteenCertificate_12161 hpn hmod
      · right
        exact nineteenCertificate_12503 hpn hmod
      · right
        exact nineteenCertificate_12541 hpn hmod
      · right
        exact nineteenCertificate_12959 hpn hmod
      · right
        exact nineteenCertificate_13187 hpn hmod
      · right
        exact nineteenCertificate_13339 hpn hmod
      · right
        exact nineteenCertificate_13567 hpn hmod
      · right
        exact nineteenCertificate_13681 hpn hmod
      · right
        exact nineteenCertificate_13757 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_03, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal03
      rcases hlocal03 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_14251 hpn hmod
      · right
        exact nineteenCertificate_14327 hpn hmod
      · right
        exact nineteenCertificate_14479 hpn hmod
      · right
        exact nineteenCertificate_14593 hpn hmod
      · right
        exact nineteenCertificate_14669 hpn hmod
      · right
        exact nineteenCertificate_14783 hpn hmod
      · right
        exact nineteenCertificate_14821 hpn hmod
      · right
        exact nineteenCertificate_14897 hpn hmod
      · right
        exact nineteenCertificate_15277 hpn hmod
      · right
        exact nineteenCertificate_15391 hpn hmod
      · right
        exact nineteenCertificate_15467 hpn hmod
      · right
        exact nineteenCertificate_15581 hpn hmod
      · right
        exact nineteenCertificate_15619 hpn hmod
      · right
        exact nineteenCertificate_15733 hpn hmod
      · right
        exact nineteenCertificate_15809 hpn hmod
      · right
        exact nineteenCertificate_15923 hpn hmod
      · right
        exact nineteenCertificate_16189 hpn hmod
      · right
        exact nineteenCertificate_16417 hpn hmod
      · right
        exact nineteenCertificate_16493 hpn hmod
      · right
        exact nineteenCertificate_16607 hpn hmod
      · right
        exact nineteenCertificate_16759 hpn hmod
      · right
        exact nineteenCertificate_16987 hpn hmod
      · right
        exact nineteenCertificate_17291 hpn hmod
      · right
        exact nineteenCertificate_17443 hpn hmod
      · right
        exact nineteenCertificate_17519 hpn hmod
      · right
        exact nineteenCertificate_17747 hpn hmod
      · right
        exact nineteenCertificate_18013 hpn hmod
      · right
        exact nineteenCertificate_18089 hpn hmod
      · right
        exact nineteenCertificate_18127 hpn hmod
      · right
        exact nineteenCertificate_18583 hpn hmod
      · right
        exact nineteenCertificate_18773 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_04, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal04
      rcases hlocal04 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_19001 hpn hmod
      · right
        exact nineteenCertificate_19267 hpn hmod
      · right
        exact nineteenCertificate_19381 hpn hmod
      · right
        exact nineteenCertificate_19457 hpn hmod
      · right
        exact nineteenCertificate_19571 hpn hmod
      · right
        exact nineteenCertificate_19609 hpn hmod
      · right
        exact nineteenCertificate_19913 hpn hmod
      · right
        exact nineteenCertificate_20369 hpn hmod
      · right
        exact nineteenCertificate_20407 hpn hmod
      · right
        exact nineteenCertificate_20483 hpn hmod
      · right
        exact nineteenCertificate_20521 hpn hmod
      · right
        exact nineteenCertificate_20749 hpn hmod
      · right
        exact nineteenCertificate_20939 hpn hmod
      · right
        exact nineteenCertificate_21319 hpn hmod
      · right
        exact nineteenCertificate_21433 hpn hmod
      · right
        exact nineteenCertificate_21661 hpn hmod
      · right
        exact nineteenCertificate_21737 hpn hmod
      · right
        exact nineteenCertificate_21851 hpn hmod
      · right
        exact nineteenCertificate_22003 hpn hmod
      · right
        exact nineteenCertificate_22079 hpn hmod
      · right
        exact nineteenCertificate_22193 hpn hmod
      · right
        exact nineteenCertificate_22307 hpn hmod
      · right
        exact nineteenCertificate_22573 hpn hmod
      · right
        exact nineteenCertificate_22877 hpn hmod
      · right
        exact nineteenCertificate_23029 hpn hmod
      · right
        exact nineteenCertificate_23143 hpn hmod
      · right
        exact nineteenCertificate_23333 hpn hmod
      · right
        exact nineteenCertificate_23371 hpn hmod
      · right
        exact nineteenCertificate_23447 hpn hmod
      · right
        exact nineteenCertificate_23561 hpn hmod
      · right
        exact nineteenCertificate_23599 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_05, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal05
      rcases hlocal05 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_23789 hpn hmod
      · right
        exact nineteenCertificate_23827 hpn hmod
      · right
        exact nineteenCertificate_24169 hpn hmod
      · right
        exact nineteenCertificate_24359 hpn hmod
      · right
        exact nineteenCertificate_24473 hpn hmod
      · right
        exact nineteenCertificate_24967 hpn hmod
      · right
        exact nineteenCertificate_25309 hpn hmod
      · right
        exact nineteenCertificate_25423 hpn hmod
      · right
        exact nineteenCertificate_25537 hpn hmod
      · right
        exact nineteenCertificate_25841 hpn hmod
      · right
        exact nineteenCertificate_26107 hpn hmod
      · right
        exact nineteenCertificate_26183 hpn hmod
      · right
        exact nineteenCertificate_26297 hpn hmod
      · right
        exact nineteenCertificate_26449 hpn hmod
      · right
        exact nineteenCertificate_26981 hpn hmod
      · right
        exact nineteenCertificate_27361 hpn hmod
      · right
        exact nineteenCertificate_27437 hpn hmod
      · right
        exact nineteenCertificate_27551 hpn hmod
      · right
        exact nineteenCertificate_27779 hpn hmod
      · right
        exact nineteenCertificate_27817 hpn hmod
      · right
        exact nineteenCertificate_27893 hpn hmod
      · right
        exact nineteenCertificate_28349 hpn hmod
      · right
        exact nineteenCertificate_28387 hpn hmod
      · right
        exact nineteenCertificate_28463 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_06, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal06
      rcases hlocal06 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_28729 hpn hmod
      · right
        exact nineteenCertificate_28843 hpn hmod
      · right
        exact nineteenCertificate_29033 hpn hmod
      · right
        exact nineteenCertificate_29147 hpn hmod
      · right
        exact nineteenCertificate_29527 hpn hmod
      · right
        exact nineteenCertificate_29641 hpn hmod
      · right
        exact nineteenCertificate_29717 hpn hmod
      · right
        exact nineteenCertificate_29983 hpn hmod
      · right
        exact nineteenCertificate_30059 hpn hmod
      · right
        exact nineteenCertificate_30097 hpn hmod
      · right
        exact nineteenCertificate_30211 hpn hmod
      · right
        exact nineteenCertificate_30553 hpn hmod
      · right
        exact nineteenCertificate_30781 hpn hmod
      · right
        exact nineteenCertificate_30971 hpn hmod
      · right
        exact nineteenCertificate_31123 hpn hmod
      · right
        exact nineteenCertificate_31237 hpn hmod
      · right
        exact nineteenCertificate_31541 hpn hmod
      · right
        exact nineteenCertificate_31769 hpn hmod
      · right
        exact nineteenCertificate_31883 hpn hmod
      · right
        exact nineteenCertificate_32377 hpn hmod
      · right
        exact nineteenCertificate_32491 hpn hmod
      · right
        exact nineteenCertificate_32719 hpn hmod
      · right
        exact nineteenCertificate_32833 hpn hmod
      · right
        exact nineteenCertificate_32909 hpn hmod
      · right
        exact nineteenCertificate_33023 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_07, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal07
      rcases hlocal07 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_33289 hpn hmod
      · right
        exact nineteenCertificate_33403 hpn hmod
      · right
        exact nineteenCertificate_33479 hpn hmod
      · right
        exact nineteenCertificate_34429 hpn hmod
      · right
        exact nineteenCertificate_34543 hpn hmod
      · right
        exact nineteenCertificate_34847 hpn hmod
      · right
        exact nineteenCertificate_34961 hpn hmod
      · right
        exact nineteenCertificate_35227 hpn hmod
      · right
        exact nineteenCertificate_35531 hpn hmod
      · right
        exact nineteenCertificate_35569 hpn hmod
      · right
        exact nineteenCertificate_35759 hpn hmod
      · right
        exact nineteenCertificate_35797 hpn hmod
      · right
        exact nineteenCertificate_35911 hpn hmod
      · right
        exact nineteenCertificate_36671 hpn hmod
      · right
        exact nineteenCertificate_36709 hpn hmod
      · right
        exact nineteenCertificate_36899 hpn hmod
      · right
        exact nineteenCertificate_37013 hpn hmod
      · right
        exact nineteenCertificate_37507 hpn hmod
      · right
        exact nineteenCertificate_37811 hpn hmod
      · right
        exact nineteenCertificate_37963 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_08, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal08
      rcases hlocal08 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_38039 hpn hmod
      · right
        exact nineteenCertificate_38153 hpn hmod
      · right
        exact nineteenCertificate_38609 hpn hmod
      · right
        exact nineteenCertificate_38723 hpn hmod
      · right
        exact nineteenCertificate_39103 hpn hmod
      · right
        exact nineteenCertificate_39217 hpn hmod
      · right
        exact nineteenCertificate_39293 hpn hmod
      · right
        exact nineteenCertificate_39521 hpn hmod
      · right
        exact nineteenCertificate_39749 hpn hmod
      · right
        exact nineteenCertificate_39863 hpn hmod
      · right
        exact nineteenCertificate_39901 hpn hmod
      · right
        exact nineteenCertificate_40129 hpn hmod
      · right
        exact nineteenCertificate_40357 hpn hmod
      · right
        exact nineteenCertificate_40433 hpn hmod
      · right
        exact nineteenCertificate_40471 hpn hmod
      · right
        exact nineteenCertificate_40699 hpn hmod
      · right
        exact nineteenCertificate_40813 hpn hmod
      · right
        exact nineteenCertificate_40927 hpn hmod
      · right
        exact nineteenCertificate_41117 hpn hmod
      · right
        exact nineteenCertificate_41231 hpn hmod
      · right
        exact nineteenCertificate_41269 hpn hmod
      · right
        exact nineteenCertificate_41611 hpn hmod
      · right
        exact nineteenCertificate_41687 hpn hmod
      · right
        exact nineteenCertificate_41801 hpn hmod
      · right
        exact nineteenCertificate_41953 hpn hmod
      · right
        exact nineteenCertificate_42181 hpn hmod
      · right
        exact nineteenCertificate_42257 hpn hmod
      · right
        exact nineteenCertificate_42409 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_09, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal09
      rcases hlocal09 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_42751 hpn hmod
      · right
        exact nineteenCertificate_42979 hpn hmod
      · right
        exact nineteenCertificate_43093 hpn hmod
      · right
        exact nineteenCertificate_43207 hpn hmod
      · right
        exact nineteenCertificate_43283 hpn hmod
      · right
        exact nineteenCertificate_43321 hpn hmod
      · right
        exact nineteenCertificate_43397 hpn hmod
      · right
        exact nineteenCertificate_43777 hpn hmod
      · right
        exact nineteenCertificate_43853 hpn hmod
      · right
        exact nineteenCertificate_43891 hpn hmod
      · right
        exact nineteenCertificate_44119 hpn hmod
      · right
        exact nineteenCertificate_44537 hpn hmod
      · right
        exact nineteenCertificate_44651 hpn hmod
      · right
        exact nineteenCertificate_44879 hpn hmod
      · right
        exact nineteenCertificate_44917 hpn hmod
      · right
        exact nineteenCertificate_45259 hpn hmod
      · right
        exact nineteenCertificate_45677 hpn hmod
      · right
        exact nineteenCertificate_45943 hpn hmod
      · right
        exact nineteenCertificate_46133 hpn hmod
      · right
        exact nineteenCertificate_46171 hpn hmod
      · right
        exact nineteenCertificate_46399 hpn hmod
      · right
        exact nineteenCertificate_46589 hpn hmod
      · right
        exact nineteenCertificate_46703 hpn hmod
      · right
        exact nineteenCertificate_46817 hpn hmod
      · right
        exact nineteenCertificate_47387 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_10, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal10
      rcases hlocal10 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_47501 hpn hmod
      · right
        exact nineteenCertificate_47653 hpn hmod
      · right
        exact nineteenCertificate_47843 hpn hmod
      · right
        exact nineteenCertificate_47881 hpn hmod
      · right
        exact nineteenCertificate_48109 hpn hmod
      · right
        exact nineteenCertificate_48299 hpn hmod
      · right
        exact nineteenCertificate_48337 hpn hmod
      · right
        exact nineteenCertificate_48413 hpn hmod
      · right
        exact nineteenCertificate_48527 hpn hmod
      · right
        exact nineteenCertificate_48679 hpn hmod
      · right
        exact nineteenCertificate_48869 hpn hmod
      · right
        exact nineteenCertificate_48907 hpn hmod
      · right
        exact nineteenCertificate_49211 hpn hmod
      · right
        exact nineteenCertificate_49363 hpn hmod
      · right
        exact nineteenCertificate_49477 hpn hmod
      · right
        exact nineteenCertificate_49667 hpn hmod
      · right
        exact nineteenCertificate_50047 hpn hmod
      · right
        exact nineteenCertificate_50123 hpn hmod
      · right
        exact nineteenCertificate_50503 hpn hmod
      · right
        exact nineteenCertificate_51263 hpn hmod
      · right
        exact nineteenCertificate_51719 hpn hmod
      · right
        exact nineteenCertificate_51871 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_11, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal11
      rcases hlocal11 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_52289 hpn hmod
      · right
        exact nineteenCertificate_52517 hpn hmod
      · right
        exact nineteenCertificate_52631 hpn hmod
      · right
        exact nineteenCertificate_52783 hpn hmod
      · right
        exact nineteenCertificate_52859 hpn hmod
      · right
        exact nineteenCertificate_52973 hpn hmod
      · right
        exact nineteenCertificate_53087 hpn hmod
      · right
        exact nineteenCertificate_53201 hpn hmod
      · right
        exact nineteenCertificate_53239 hpn hmod
      · right
        exact nineteenCertificate_53353 hpn hmod
      · right
        exact nineteenCertificate_53657 hpn hmod
      · right
        exact nineteenCertificate_53923 hpn hmod
      · right
        exact nineteenCertificate_54037 hpn hmod
      · right
        exact nineteenCertificate_54151 hpn hmod
      · right
        exact nineteenCertificate_54493 hpn hmod
      · right
        exact nineteenCertificate_54721 hpn hmod
      · right
        exact nineteenCertificate_54949 hpn hmod
      · right
        exact nineteenCertificate_55291 hpn hmod
      · right
        exact nineteenCertificate_55633 hpn hmod
      · right
        exact nineteenCertificate_55823 hpn hmod
      · right
        exact nineteenCertificate_56393 hpn hmod
      · right
        exact nineteenCertificate_56431 hpn hmod
      · right
        exact nineteenCertificate_56659 hpn hmod
      · right
        exact nineteenCertificate_56773 hpn hmod
      · right
        exact nineteenCertificate_56963 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_12, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal12
      rcases hlocal12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_57077 hpn hmod
      · right
        exact nineteenCertificate_57191 hpn hmod
      · right
        exact nineteenCertificate_57457 hpn hmod
      · right
        exact nineteenCertificate_57571 hpn hmod
      · right
        exact nineteenCertificate_58027 hpn hmod
      · right
        exact nineteenCertificate_58217 hpn hmod
      · right
        exact nineteenCertificate_58369 hpn hmod
      · right
        exact nineteenCertificate_58711 hpn hmod
      · right
        exact nineteenCertificate_58787 hpn hmod
      · right
        exact nineteenCertificate_58901 hpn hmod
      · right
        exact nineteenCertificate_59053 hpn hmod
      · right
        exact nineteenCertificate_59167 hpn hmod
      · right
        exact nineteenCertificate_59243 hpn hmod
      · right
        exact nineteenCertificate_59281 hpn hmod
      · right
        exact nineteenCertificate_59357 hpn hmod
      · right
        exact nineteenCertificate_59471 hpn hmod
      · right
        exact nineteenCertificate_59509 hpn hmod
      · right
        exact nineteenCertificate_59699 hpn hmod
      · right
        exact nineteenCertificate_60041 hpn hmod
      · right
        exact nineteenCertificate_60383 hpn hmod
      · right
        exact nineteenCertificate_60497 hpn hmod
      · right
        exact nineteenCertificate_60611 hpn hmod
      · right
        exact nineteenCertificate_60649 hpn hmod
      · right
        exact nineteenCertificate_60763 hpn hmod
      · right
        exact nineteenCertificate_60953 hpn hmod
      · right
        exact nineteenCertificate_61333 hpn hmod
      · right
        exact nineteenCertificate_61409 hpn hmod
      · right
        exact nineteenCertificate_61561 hpn hmod
      · right
        exact nineteenCertificate_61637 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_13, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal13
      rcases hlocal13 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_61751 hpn hmod
      · right
        exact nineteenCertificate_61979 hpn hmod
      · right
        exact nineteenCertificate_62017 hpn hmod
      · right
        exact nineteenCertificate_62131 hpn hmod
      · right
        exact nineteenCertificate_62207 hpn hmod
      · right
        exact nineteenCertificate_62473 hpn hmod
      · right
        exact nineteenCertificate_62549 hpn hmod
      · right
        exact nineteenCertificate_62701 hpn hmod
      · right
        exact nineteenCertificate_62929 hpn hmod
      · right
        exact nineteenCertificate_63347 hpn hmod
      · right
        exact nineteenCertificate_63499 hpn hmod
      · right
        exact nineteenCertificate_63689 hpn hmod
      · right
        exact nineteenCertificate_63727 hpn hmod
      · right
        exact nineteenCertificate_63803 hpn hmod
      · right
        exact nineteenCertificate_63841 hpn hmod
      · right
        exact nineteenCertificate_64373 hpn hmod
      · right
        exact nineteenCertificate_64601 hpn hmod
      · right
        exact nineteenCertificate_65171 hpn hmod
      · right
        exact nineteenCertificate_65323 hpn hmod
      · right
        exact nineteenCertificate_65437 hpn hmod
      · right
        exact nineteenCertificate_65551 hpn hmod
      · right
        exact nineteenCertificate_66083 hpn hmod
      · right
        exact nineteenCertificate_66463 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_14, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal14
      rcases hlocal14 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_66653 hpn hmod
      · right
        exact nineteenCertificate_66919 hpn hmod
      · right
        exact nineteenCertificate_67033 hpn hmod
      · right
        exact nineteenCertificate_67261 hpn hmod
      · right
        exact nineteenCertificate_67489 hpn hmod
      · right
        exact nineteenCertificate_67679 hpn hmod
      · right
        exact nineteenCertificate_68059 hpn hmod
      · right
        exact nineteenCertificate_68477 hpn hmod
      · right
        exact nineteenCertificate_68743 hpn hmod
      · right
        exact nineteenCertificate_68819 hpn hmod
      · right
        exact nineteenCertificate_69313 hpn hmod
      · right
        exact nineteenCertificate_69389 hpn hmod
      · right
        exact nineteenCertificate_69427 hpn hmod
      · right
        exact nineteenCertificate_69959 hpn hmod
      · right
        exact nineteenCertificate_69997 hpn hmod
      · right
        exact nineteenCertificate_70111 hpn hmod
      · right
        exact nineteenCertificate_70529 hpn hmod
      · right
        exact nineteenCertificate_71023 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_15, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal15
      rcases hlocal15 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_71327 hpn hmod
      · right
        exact nineteenCertificate_71479 hpn hmod
      · right
        exact nineteenCertificate_71593 hpn hmod
      · right
        exact nineteenCertificate_71707 hpn hmod
      · right
        exact nineteenCertificate_71821 hpn hmod
      · right
        exact nineteenCertificate_72277 hpn hmod
      · right
        exact nineteenCertificate_72353 hpn hmod
      · right
        exact nineteenCertificate_72467 hpn hmod
      · right
        exact nineteenCertificate_72733 hpn hmod
      · right
        exact nineteenCertificate_72923 hpn hmod
      · right
        exact nineteenCertificate_73037 hpn hmod
      · right
        exact nineteenCertificate_73189 hpn hmod
      · right
        exact nineteenCertificate_73303 hpn hmod
      · right
        exact nineteenCertificate_73379 hpn hmod
      · right
        exact nineteenCertificate_73417 hpn hmod
      · right
        exact nineteenCertificate_73607 hpn hmod
      · right
        exact nineteenCertificate_73721 hpn hmod
      · right
        exact nineteenCertificate_74101 hpn hmod
      · right
        exact nineteenCertificate_74177 hpn hmod
      · right
        exact nineteenCertificate_74747 hpn hmod
      · right
        exact nineteenCertificate_74861 hpn hmod
      · right
        exact nineteenCertificate_75013 hpn hmod
      · right
        exact nineteenCertificate_75431 hpn hmod
      · right
        exact nineteenCertificate_75583 hpn hmod
      · right
        exact nineteenCertificate_75659 hpn hmod
      · right
        exact nineteenCertificate_75773 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_16, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal16
      rcases hlocal16 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_76001 hpn hmod
      · right
        exact nineteenCertificate_76039 hpn hmod
      · right
        exact nineteenCertificate_76343 hpn hmod
      · right
        exact nineteenCertificate_76837 hpn hmod
      · right
        exact nineteenCertificate_76913 hpn hmod
      · right
        exact nineteenCertificate_77141 hpn hmod
      · right
        exact nineteenCertificate_77369 hpn hmod
      · right
        exact nineteenCertificate_77521 hpn hmod
      · right
        exact nineteenCertificate_77711 hpn hmod
      · right
        exact nineteenCertificate_77863 hpn hmod
      · right
        exact nineteenCertificate_77977 hpn hmod
      · right
        exact nineteenCertificate_78167 hpn hmod
      · right
        exact nineteenCertificate_78509 hpn hmod
      · right
        exact nineteenCertificate_78623 hpn hmod
      · right
        exact nineteenCertificate_78737 hpn hmod
      · right
        exact nineteenCertificate_78889 hpn hmod
      · right
        exact nineteenCertificate_79193 hpn hmod
      · right
        exact nineteenCertificate_79231 hpn hmod
      · right
        exact nineteenCertificate_79687 hpn hmod
      · right
        exact nineteenCertificate_79801 hpn hmod
      · right
        exact nineteenCertificate_80447 hpn hmod
      · right
        exact nineteenCertificate_80599 hpn hmod
      · right
        exact nineteenCertificate_80713 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_17, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal17
      rcases hlocal17 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_80789 hpn hmod
      · right
        exact nineteenCertificate_81017 hpn hmod
      · right
        exact nineteenCertificate_81131 hpn hmod
      · right
        exact nineteenCertificate_81283 hpn hmod
      · right
        exact nineteenCertificate_81359 hpn hmod
      · right
        exact nineteenCertificate_81701 hpn hmod
      · right
        exact nineteenCertificate_81853 hpn hmod
      · right
        exact nineteenCertificate_81929 hpn hmod
      · right
        exact nineteenCertificate_81967 hpn hmod
      · right
        exact nineteenCertificate_82499 hpn hmod
      · right
        exact nineteenCertificate_82613 hpn hmod
      · right
        exact nineteenCertificate_82651 hpn hmod
      · right
        exact nineteenCertificate_82727 hpn hmod
      · right
        exact nineteenCertificate_83221 hpn hmod
      · right
        exact nineteenCertificate_83449 hpn hmod
      · right
        exact nineteenCertificate_83563 hpn hmod
      · right
        exact nineteenCertificate_83639 hpn hmod
      · right
        exact nineteenCertificate_83791 hpn hmod
      · right
        exact nineteenCertificate_84247 hpn hmod
      · right
        exact nineteenCertificate_84437 hpn hmod
      · right
        exact nineteenCertificate_84551 hpn hmod
      · right
        exact nineteenCertificate_84589 hpn hmod
      · right
        exact nineteenCertificate_85121 hpn hmod
      · right
        exact nineteenCertificate_85159 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_18, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal18
      rcases hlocal18 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_85577 hpn hmod
      · right
        exact nineteenCertificate_85691 hpn hmod
      · right
        exact nineteenCertificate_85843 hpn hmod
      · right
        exact nineteenCertificate_86413 hpn hmod
      · right
        exact nineteenCertificate_86869 hpn hmod
      · right
        exact nineteenCertificate_87211 hpn hmod
      · right
        exact nineteenCertificate_87553 hpn hmod
      · right
        exact nineteenCertificate_87629 hpn hmod
      · right
        exact nineteenCertificate_87743 hpn hmod
      · right
        exact nineteenCertificate_88237 hpn hmod
      · right
        exact nineteenCertificate_88427 hpn hmod
      · right
        exact nineteenCertificate_88807 hpn hmod
      · right
        exact nineteenCertificate_88883 hpn hmod
      · right
        exact nineteenCertificate_88997 hpn hmod
      · right
        exact nineteenCertificate_89491 hpn hmod
      · right
        exact nineteenCertificate_89567 hpn hmod
      · right
        exact nineteenCertificate_89681 hpn hmod
      · right
        exact nineteenCertificate_89833 hpn hmod
      · right
        exact nineteenCertificate_89909 hpn hmod
      · right
        exact nineteenCertificate_90023 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_19, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal19
      rcases hlocal19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_90289 hpn hmod
      · right
        exact nineteenCertificate_90403 hpn hmod
      · right
        exact nineteenCertificate_90631 hpn hmod
      · right
        exact nineteenCertificate_90821 hpn hmod
      · right
        exact nineteenCertificate_91163 hpn hmod
      · right
        exact nineteenCertificate_91733 hpn hmod
      · right
        exact nineteenCertificate_91771 hpn hmod
      · right
        exact nineteenCertificate_91961 hpn hmod
      · right
        exact nineteenCertificate_92189 hpn hmod
      · right
        exact nineteenCertificate_92227 hpn hmod
      · right
        exact nineteenCertificate_92569 hpn hmod
      · right
        exact nineteenCertificate_92683 hpn hmod
      · right
        exact nineteenCertificate_92987 hpn hmod
      · right
        exact nineteenCertificate_93139 hpn hmod
      · right
        exact nineteenCertificate_93253 hpn hmod
      · right
        exact nineteenCertificate_93329 hpn hmod
      · right
        exact nineteenCertificate_93481 hpn hmod
      · right
        exact nineteenCertificate_93557 hpn hmod
      · right
        exact nineteenCertificate_93937 hpn hmod
      · right
        exact nineteenCertificate_94583 hpn hmod
      · right
        exact nineteenCertificate_94621 hpn hmod
      · right
        exact nineteenCertificate_94811 hpn hmod
      · right
        exact nineteenCertificate_94849 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_20, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal20
      rcases hlocal20 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_95153 hpn hmod
      · right
        exact nineteenCertificate_95191 hpn hmod
      · right
        exact nineteenCertificate_95267 hpn hmod
      · right
        exact nineteenCertificate_95419 hpn hmod
      · right
        exact nineteenCertificate_95723 hpn hmod
      · right
        exact nineteenCertificate_95989 hpn hmod
      · right
        exact nineteenCertificate_96179 hpn hmod
      · right
        exact nineteenCertificate_96293 hpn hmod
      · right
        exact nineteenCertificate_96331 hpn hmod
      · right
        exact nineteenCertificate_96749 hpn hmod
      · right
        exact nineteenCertificate_96787 hpn hmod
      · right
        exact nineteenCertificate_97547 hpn hmod
      · right
        exact nineteenCertificate_97813 hpn hmod
      · right
        exact nineteenCertificate_97927 hpn hmod
      · right
        exact nineteenCertificate_98041 hpn hmod
      · right
        exact nineteenCertificate_98269 hpn hmod
      · right
        exact nineteenCertificate_98459 hpn hmod
      · right
        exact nineteenCertificate_98573 hpn hmod
      · right
        exact nineteenCertificate_98801 hpn hmod
      · right
        exact nineteenCertificate_98953 hpn hmod
      · right
        exact nineteenCertificate_99181 hpn hmod
      · right
        exact nineteenCertificate_99257 hpn hmod
      · right
        exact nineteenCertificate_99371 hpn hmod
      · right
        exact nineteenCertificate_99409 hpn hmod
      · right
        exact nineteenCertificate_99523 hpn hmod
      · right
        exact nineteenCertificate_99713 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_21, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal21
      rcases hlocal21 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_100169 hpn hmod
      · right
        exact nineteenCertificate_100207 hpn hmod
      · right
        exact nineteenCertificate_100511 hpn hmod
      · right
        exact nineteenCertificate_100549 hpn hmod
      · right
        exact nineteenCertificate_100853 hpn hmod
      · right
        exact nineteenCertificate_101081 hpn hmod
      · right
        exact nineteenCertificate_101119 hpn hmod
      · right
        exact nineteenCertificate_101347 hpn hmod
      · right
        exact nineteenCertificate_101537 hpn hmod
      · right
        exact nineteenCertificate_101879 hpn hmod
      · right
        exact nineteenCertificate_101917 hpn hmod
      · right
        exact nineteenCertificate_102031 hpn hmod
      · right
        exact nineteenCertificate_102107 hpn hmod
      · right
        exact nineteenCertificate_102259 hpn hmod
      · right
        exact nineteenCertificate_102563 hpn hmod
      · right
        exact nineteenCertificate_102677 hpn hmod
      · right
        exact nineteenCertificate_102829 hpn hmod
      · right
        exact nineteenCertificate_103171 hpn hmod
      · right
        exact nineteenCertificate_103399 hpn hmod
      · right
        exact nineteenCertificate_103703 hpn hmod
      · right
        exact nineteenCertificate_103969 hpn hmod
      · right
        exact nineteenCertificate_104311 hpn hmod
    · simp only [exceptionalSplitPrimesNineteen_22, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hlocal22
      rcases hlocal22 with rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_104729 hpn hmod
      · right
        exact nineteenCertificate_105071 hpn hmod
      · right
        exact nineteenCertificate_105337 hpn hmod
      · right
        exact nineteenCertificate_105527 hpn hmod
      · right
        exact nineteenCertificate_105907 hpn hmod
  · by_cases hmem : p ∈ exceptionalNonSplitPrimesNineteen
    · simp only [exceptionalNonSplitPrimesNineteen, List.mem_toFinset, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      · right
        exact nineteenCertificate_7 hpn
      · right
        exact nineteenCertificate_11 hpn
      · right
        exact nineteenCertificate_37 hpn
      · right
        exact nineteenCertificate_113 hpn
      · right
        exact nineteenCertificate_151 hpn
      · right
        exact nineteenCertificate_227 hpn
    · left
      exact log_lt_orderOf_nineteen_of_mod_ne_one hp hpn
        (Finset.mem_Icc.mp hple).2 hmod hmem

set_option backward.isDefEq.respectTransparency false in
theorem isRegularPrime_nineteen :
    haveI : Fact (Nat.Prime 19) := ⟨Nat.prime_nineteen⟩
    IsRegularPrime 19 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2 (Rat.nineteen_pid (CyclotomicField _ ℚ))

theorem fermatLastTheoremNineteen : FermatLastTheoremFor 19 :=
  @flt_regular 19 ⟨Nat.prime_nineteen⟩ isRegularPrime_nineteen (by omega)
