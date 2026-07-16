import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum.Prime

set_option linter.style.longLine false

/-! Finite prime data shared by the independently compiled p = 19 bound checks. -/

open Finset

/-! The exceptional primes that do not split completely modulo 19. The primes
`7` and `11` have order three; the other four have order two. -/

def exceptionalNonSplitPrimesNineteen : Finset ℕ :=
  [7, 11, 37, 113, 151, 227].toFinset

/-! The 552 split exceptional primes, partitioned by the classifier's k ranges. -/

def exceptionalSplitPrimesNineteen_00 : Finset ℕ :=
  [191, 229, 419, 457, 571, 647, 761, 1103, 1217, 1483, 1559, 1597, 1787, 1901, 2053, 2129, 2243,
    2281, 2357, 2699, 2851, 2927, 3041, 3079, 3307, 3877, 4219, 4409, 4447, 4523, 4561, 4637].toFinset

def exceptionalSplitPrimesNineteen_01 : Finset ℕ :=
  [4751, 4789, 4903, 5701, 6043, 6271, 6689, 6803, 6841, 6917, 7069, 7297, 7411, 7487, 7639, 7753,
    7829, 7867, 8171, 8209, 8513, 8627, 8741, 8779, 8893, 8969, 9007, 9311, 9349, 9463].toFinset

def exceptionalSplitPrimesNineteen_02 : Finset ℕ :=
  [9539, 9767, 10223, 10337, 10831, 11059, 11173, 11287, 11743, 11933, 11971, 12161, 12503, 12541,
    12959, 13187, 13339, 13567, 13681, 13757].toFinset

def exceptionalSplitPrimesNineteen_03 : Finset ℕ :=
  [14251, 14327, 14479, 14593, 14669, 14783, 14821, 14897, 15277, 15391, 15467, 15581, 15619, 15733,
    15809, 15923, 16189, 16417, 16493, 16607, 16759, 16987, 17291, 17443, 17519, 17747, 18013,
    18089, 18127, 18583, 18773].toFinset

def exceptionalSplitPrimesNineteen_04 : Finset ℕ :=
  [19001, 19267, 19381, 19457, 19571, 19609, 19913, 20369, 20407, 20483, 20521, 20749, 20939, 21319,
    21433, 21661, 21737, 21851, 22003, 22079, 22193, 22307, 22573, 22877, 23029, 23143, 23333,
    23371, 23447, 23561, 23599].toFinset

def exceptionalSplitPrimesNineteen_05 : Finset ℕ :=
  [23789, 23827, 24169, 24359, 24473, 24967, 25309, 25423, 25537, 25841, 26107, 26183, 26297, 26449,
    26981, 27361, 27437, 27551, 27779, 27817, 27893, 28349, 28387, 28463].toFinset

def exceptionalSplitPrimesNineteen_06 : Finset ℕ :=
  [28729, 28843, 29033, 29147, 29527, 29641, 29717, 29983, 30059, 30097, 30211, 30553, 30781, 30971,
    31123, 31237, 31541, 31769, 31883, 32377, 32491, 32719, 32833, 32909, 33023].toFinset

def exceptionalSplitPrimesNineteen_07 : Finset ℕ :=
  [33289, 33403, 33479, 34429, 34543, 34847, 34961, 35227, 35531, 35569, 35759, 35797, 35911, 36671,
    36709, 36899, 37013, 37507, 37811, 37963].toFinset

def exceptionalSplitPrimesNineteen_08 : Finset ℕ :=
  [38039, 38153, 38609, 38723, 39103, 39217, 39293, 39521, 39749, 39863, 39901, 40129, 40357, 40433,
    40471, 40699, 40813, 40927, 41117, 41231, 41269, 41611, 41687, 41801, 41953, 42181, 42257, 42409].toFinset

def exceptionalSplitPrimesNineteen_09 : Finset ℕ :=
  [42751, 42979, 43093, 43207, 43283, 43321, 43397, 43777, 43853, 43891, 44119, 44537, 44651, 44879,
    44917, 45259, 45677, 45943, 46133, 46171, 46399, 46589, 46703, 46817, 47387].toFinset

def exceptionalSplitPrimesNineteen_10 : Finset ℕ :=
  [47501, 47653, 47843, 47881, 48109, 48299, 48337, 48413, 48527, 48679, 48869, 48907, 49211, 49363,
    49477, 49667, 50047, 50123, 50503, 51263, 51719, 51871].toFinset

def exceptionalSplitPrimesNineteen_11 : Finset ℕ :=
  [52289, 52517, 52631, 52783, 52859, 52973, 53087, 53201, 53239, 53353, 53657, 53923, 54037, 54151,
    54493, 54721, 54949, 55291, 55633, 55823, 56393, 56431, 56659, 56773, 56963].toFinset

def exceptionalSplitPrimesNineteen_12 : Finset ℕ :=
  [57077, 57191, 57457, 57571, 58027, 58217, 58369, 58711, 58787, 58901, 59053, 59167, 59243, 59281,
    59357, 59471, 59509, 59699, 60041, 60383, 60497, 60611, 60649, 60763, 60953, 61333, 61409,
    61561, 61637].toFinset

def exceptionalSplitPrimesNineteen_13 : Finset ℕ :=
  [61751, 61979, 62017, 62131, 62207, 62473, 62549, 62701, 62929, 63347, 63499, 63689, 63727, 63803,
    63841, 64373, 64601, 65171, 65323, 65437, 65551, 66083, 66463].toFinset

def exceptionalSplitPrimesNineteen_14 : Finset ℕ :=
  [66653, 66919, 67033, 67261, 67489, 67679, 68059, 68477, 68743, 68819, 69313, 69389, 69427, 69959,
    69997, 70111, 70529, 71023].toFinset

def exceptionalSplitPrimesNineteen_15 : Finset ℕ :=
  [71327, 71479, 71593, 71707, 71821, 72277, 72353, 72467, 72733, 72923, 73037, 73189, 73303, 73379,
    73417, 73607, 73721, 74101, 74177, 74747, 74861, 75013, 75431, 75583, 75659, 75773].toFinset

def exceptionalSplitPrimesNineteen_16 : Finset ℕ :=
  [76001, 76039, 76343, 76837, 76913, 77141, 77369, 77521, 77711, 77863, 77977, 78167, 78509, 78623,
    78737, 78889, 79193, 79231, 79687, 79801, 80447, 80599, 80713].toFinset

def exceptionalSplitPrimesNineteen_17 : Finset ℕ :=
  [80789, 81017, 81131, 81283, 81359, 81701, 81853, 81929, 81967, 82499, 82613, 82651, 82727, 83221,
    83449, 83563, 83639, 83791, 84247, 84437, 84551, 84589, 85121, 85159].toFinset

def exceptionalSplitPrimesNineteen_18 : Finset ℕ :=
  [85577, 85691, 85843, 86413, 86869, 87211, 87553, 87629, 87743, 88237, 88427, 88807, 88883, 88997,
    89491, 89567, 89681, 89833, 89909, 90023].toFinset

def exceptionalSplitPrimesNineteen_19 : Finset ℕ :=
  [90289, 90403, 90631, 90821, 91163, 91733, 91771, 91961, 92189, 92227, 92569, 92683, 92987, 93139,
    93253, 93329, 93481, 93557, 93937, 94583, 94621, 94811, 94849].toFinset

def exceptionalSplitPrimesNineteen_20 : Finset ℕ :=
  [95153, 95191, 95267, 95419, 95723, 95989, 96179, 96293, 96331, 96749, 96787, 97547, 97813, 97927,
    98041, 98269, 98459, 98573, 98801, 98953, 99181, 99257, 99371, 99409, 99523, 99713].toFinset

def exceptionalSplitPrimesNineteen_21 : Finset ℕ :=
  [100169, 100207, 100511, 100549, 100853, 101081, 101119, 101347, 101537, 101879, 101917, 102031,
    102107, 102259, 102563, 102677, 102829, 103171, 103399, 103703, 103969, 104311].toFinset

def exceptionalSplitPrimesNineteen_22 : Finset ℕ :=
  [104729, 105071, 105337, 105527, 105907].toFinset

def exceptionalSplitPrimesNineteen : Finset ℕ :=
  exceptionalSplitPrimesNineteen_00 ∪ (exceptionalSplitPrimesNineteen_01 ∪ (exceptionalSplitPrimesNineteen_02 ∪ (exceptionalSplitPrimesNineteen_03 ∪ (exceptionalSplitPrimesNineteen_04 ∪ (exceptionalSplitPrimesNineteen_05 ∪ (exceptionalSplitPrimesNineteen_06 ∪ (exceptionalSplitPrimesNineteen_07 ∪ (exceptionalSplitPrimesNineteen_08 ∪ (exceptionalSplitPrimesNineteen_09 ∪ (exceptionalSplitPrimesNineteen_10 ∪ (exceptionalSplitPrimesNineteen_11 ∪ (exceptionalSplitPrimesNineteen_12 ∪ (exceptionalSplitPrimesNineteen_13 ∪ (exceptionalSplitPrimesNineteen_14 ∪ (exceptionalSplitPrimesNineteen_15 ∪ (exceptionalSplitPrimesNineteen_16 ∪ (exceptionalSplitPrimesNineteen_17 ∪ (exceptionalSplitPrimesNineteen_18 ∪ (exceptionalSplitPrimesNineteen_19 ∪ (exceptionalSplitPrimesNineteen_20 ∪ (exceptionalSplitPrimesNineteen_21 ∪ (exceptionalSplitPrimesNineteen_22))))))))))))))))))))))

/-! All 558 exceptional primes, split and non-split. -/

def exceptionalPrimesNineteen : Finset ℕ :=
  exceptionalNonSplitPrimesNineteen ∪ exceptionalSplitPrimesNineteen

/-! Structural inclusions used to lift each inexpensive local classification. -/

theorem exceptionalSplitPrimesNineteen_00_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_00) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inl hp

theorem exceptionalSplitPrimesNineteen_01_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_01) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inl hp)

theorem exceptionalSplitPrimesNineteen_02_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_02) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inl hp))

theorem exceptionalSplitPrimesNineteen_03_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_03) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inl hp)))

theorem exceptionalSplitPrimesNineteen_04_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_04) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))

theorem exceptionalSplitPrimesNineteen_05_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_05) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))

theorem exceptionalSplitPrimesNineteen_06_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_06) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))

theorem exceptionalSplitPrimesNineteen_07_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_07) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))

theorem exceptionalSplitPrimesNineteen_08_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_08) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))))

theorem exceptionalSplitPrimesNineteen_09_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_09) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))))

theorem exceptionalSplitPrimesNineteen_10_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_10) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))))))

theorem exceptionalSplitPrimesNineteen_11_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_11) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))))))

theorem exceptionalSplitPrimesNineteen_12_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_12) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))))))))

theorem exceptionalSplitPrimesNineteen_13_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_13) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))))))))

theorem exceptionalSplitPrimesNineteen_14_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_14) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))))))))))

theorem exceptionalSplitPrimesNineteen_15_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_15) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))))))))))

theorem exceptionalSplitPrimesNineteen_16_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_16) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))))))))))))

theorem exceptionalSplitPrimesNineteen_17_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_17) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))))))))))))

theorem exceptionalSplitPrimesNineteen_18_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_18) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))))))))))))))

theorem exceptionalSplitPrimesNineteen_19_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_19) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))))))))))))))

theorem exceptionalSplitPrimesNineteen_20_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_20) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))))))))))))))))

theorem exceptionalSplitPrimesNineteen_21_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_21) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))))))))))))))))

theorem exceptionalSplitPrimesNineteen_22_mem {p : ℕ}
    (hp : p ∈ exceptionalSplitPrimesNineteen_22) : p ∈ exceptionalSplitPrimesNineteen := by
  simp only [exceptionalSplitPrimesNineteen, Finset.mem_union]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hp))))))))))))))))))))))
