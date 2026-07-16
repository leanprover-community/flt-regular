import BealRegular.NineteenPrimeClassification00
import BealRegular.NineteenPrimeClassification01
import BealRegular.NineteenPrimeClassification02
import BealRegular.NineteenPrimeClassification03
import BealRegular.NineteenPrimeClassification04
import BealRegular.NineteenPrimeClassification05
import BealRegular.NineteenPrimeClassification06
import BealRegular.NineteenPrimeClassification07
import BealRegular.NineteenPrimeClassification08
import BealRegular.NineteenPrimeClassification09
import BealRegular.NineteenPrimeClassification10
import BealRegular.NineteenPrimeClassification11
import BealRegular.NineteenPrimeClassification12
import BealRegular.NineteenPrimeClassification13
import BealRegular.NineteenPrimeClassification14
import BealRegular.NineteenPrimeClassification15
import BealRegular.NineteenPrimeClassification16
import BealRegular.NineteenPrimeClassification17
import BealRegular.NineteenPrimeClassification18
import BealRegular.NineteenPrimeClassification19
import BealRegular.NineteenPrimeClassification20
import BealRegular.NineteenPrimeClassification21
import BealRegular.NineteenPrimeClassification22
import BealRegular.NineteenPrimeClassification23
import BealRegular.NineteenPrimeClassification24
import BealRegular.NineteenPrimeClassification25
import BealRegular.NineteenPrimeClassification26
import BealRegular.NineteenPrimeClassification27
import BealRegular.NineteenPrimeClassification28
import BealRegular.NineteenPrimeClassification29
import BealRegular.NineteenPrimeClassification30
import BealRegular.NineteenPrimeClassification31
import BealRegular.NineteenPrimeClassification32
import BealRegular.NineteenPrimeClassification33
import BealRegular.NineteenPrimeClassification34
import BealRegular.NineteenPrimeClassification35
import BealRegular.NineteenPrimeClassification36
import BealRegular.NineteenPrimeClassification37
import BealRegular.NineteenPrimeClassification38
import BealRegular.NineteenPrimeClassification39
import BealRegular.NineteenPrimeClassification40
import BealRegular.NineteenPrimeClassification41
import BealRegular.NineteenPrimeClassification42
import BealRegular.NineteenPrimeClassification43
import BealRegular.NineteenPrimeClassification44

/-! Composition of the independently compiled p = 19 split-prime classifiers. -/

set_option linter.style.longLine false in
set_option maxRecDepth 20000 in
theorem prime_mem_exceptionalSplitPrimesNineteen_of_k_le {k : ℕ}
    (hk : k ≤ 5575) (hprime : (19 * k + 1).Prime) :
    19 * k + 1 ∈ exceptionalSplitPrimesNineteen := by
  have hranges :
      (0 ≤ k ∧ k ≤ 124) ∨
      (125 ≤ k ∧ k ≤ 249) ∨
      (250 ≤ k ∧ k ≤ 374) ∨
      (375 ≤ k ∧ k ≤ 499) ∨
      (500 ≤ k ∧ k ≤ 624) ∨
      (625 ≤ k ∧ k ≤ 749) ∨
      (750 ≤ k ∧ k ≤ 874) ∨
      (875 ≤ k ∧ k ≤ 999) ∨
      (1000 ≤ k ∧ k ≤ 1124) ∨
      (1125 ≤ k ∧ k ≤ 1249) ∨
      (1250 ≤ k ∧ k ≤ 1374) ∨
      (1375 ≤ k ∧ k ≤ 1499) ∨
      (1500 ≤ k ∧ k ≤ 1624) ∨
      (1625 ≤ k ∧ k ≤ 1749) ∨
      (1750 ≤ k ∧ k ≤ 1874) ∨
      (1875 ≤ k ∧ k ≤ 1999) ∨
      (2000 ≤ k ∧ k ≤ 2124) ∨
      (2125 ≤ k ∧ k ≤ 2249) ∨
      (2250 ≤ k ∧ k ≤ 2374) ∨
      (2375 ≤ k ∧ k ≤ 2499) ∨
      (2500 ≤ k ∧ k ≤ 2624) ∨
      (2625 ≤ k ∧ k ≤ 2749) ∨
      (2750 ≤ k ∧ k ≤ 2874) ∨
      (2875 ≤ k ∧ k ≤ 2999) ∨
      (3000 ≤ k ∧ k ≤ 3124) ∨
      (3125 ≤ k ∧ k ≤ 3249) ∨
      (3250 ≤ k ∧ k ≤ 3374) ∨
      (3375 ≤ k ∧ k ≤ 3499) ∨
      (3500 ≤ k ∧ k ≤ 3624) ∨
      (3625 ≤ k ∧ k ≤ 3749) ∨
      (3750 ≤ k ∧ k ≤ 3874) ∨
      (3875 ≤ k ∧ k ≤ 3999) ∨
      (4000 ≤ k ∧ k ≤ 4124) ∨
      (4125 ≤ k ∧ k ≤ 4249) ∨
      (4250 ≤ k ∧ k ≤ 4374) ∨
      (4375 ≤ k ∧ k ≤ 4499) ∨
      (4500 ≤ k ∧ k ≤ 4624) ∨
      (4625 ≤ k ∧ k ≤ 4749) ∨
      (4750 ≤ k ∧ k ≤ 4874) ∨
      (4875 ≤ k ∧ k ≤ 4999) ∨
      (5000 ≤ k ∧ k ≤ 5124) ∨
      (5125 ≤ k ∧ k ≤ 5249) ∨
      (5250 ≤ k ∧ k ≤ 5374) ∨
      (5375 ≤ k ∧ k ≤ 5499) ∨
      (5500 ≤ k ∧ k ≤ 5575) := by
    omega
  rcases hranges with hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange | hrange
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_00 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_00_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_01 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_00_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_02 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_01_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_03 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_01_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_04 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_02_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_05 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_02_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_06 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_03_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_07 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_03_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_08 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_04_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_09 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_04_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_10 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_05_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_11 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_05_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_12 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_06_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_13 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_06_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_14 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_07_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_15 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_07_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_16 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_08_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_17 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_08_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_18 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_09_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_19 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_09_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_20 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_10_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_21 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_10_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_22 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_11_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_23 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_11_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_24 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_12_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_25 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_12_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_26 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_13_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_27 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_13_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_28 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_14_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_29 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_14_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_30 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_15_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_31 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_15_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_32 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_16_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_33 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_16_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_34 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_17_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_35 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_17_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_36 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_18_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_37 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_18_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_38 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_19_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_39 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_19_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_40 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_20_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_41 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_20_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_42 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_21_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_43 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_21_mem hlocal
  · have hlocal := prime_mem_exceptionalSplitPrimesNineteen_44 k
      (by simpa only [Finset.mem_Icc] using hrange) hprime
    exact exceptionalSplitPrimesNineteen_22_mem hlocal
