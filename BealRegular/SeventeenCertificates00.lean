import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 2 through 613. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_2 [Fact (Nat.Prime 2)]
    (hpn : 2 ≠ 17) : SeventeenCertificate 2 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X^8 + X^5 + X^4 + X^3 + 1
  let Q : ℤ[X] := X^8 + X^7 + X^6 - X^4 - 2*X^3 - X^2 + X + 3
  let A : ℤ[X] := 2*X^7 + X^6 - X^5 - X^4 + X^2 - 1
  let G : ℤ[X] := X^14 + X^8 + X^4 + X^3 + X^2 + X
  let Qp : ℤ[X] := -X^15 - X^14 - X^11 - 2*X^10 - X^7 - X^6 - X^5 - 2*X^2 - X
  let Rp : ℤ[X] := X^13 - X^11 + X^9 + X^8 - X^7 + 2*X^3 + X^2 - 2*X + 2
  let QP : ℤ[X] := -2*X^15 - 2*X^14 - X^13 - X^11 - 3*X^10 - X^9 - X^7 - 2*X^6 - 2*X^5 - 2*X^2 - 2*X
  let RP : ℤ[X] := 2*X^13 - X^11 - X^10 + X^9 + 2*X^8 - X^6 + 3*X^3 + 2*X^2 - X + 1
  let C1 : ℤ[X] := X^6 - X^3 - X^2 - X + 2
  let C2 : ℤ[X] := X^7 + X^6 + X^2 + X - 1
  let d := 8
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
    have hn : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
    fin_cases hn <;> decide +revert
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_67 [Fact (Nat.Prime 67)]
    (hpn : 67 ≠ 17) : SeventeenCertificate 67 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X^2 - 13*X + 1
  let Q : ℤ[X] := X^14 + 14*X^13 + 182*X^12 + 2353*X^11 + 30408*X^10 + 392952*X^9 + 5077969*X^8
    + 65620646*X^7 + 847990430*X^6 + 10958254945*X^5 + 141609323856*X^4 + 1829962955184*X^3
    + 23647909093537*X^2 + 305592855260798*X + 3949059209296838
  let A : ℤ[X] := 761674281576091*X - 58941182228311
  let G : ℤ[X] := -X^15 - X^13 - X^11 - X^9 - X^7 - X^4 - X^3 - X^2 - X
  let Qp : ℤ[X] := 8*X^15 + 8*X^14 + 30*X^12 + 26*X^11 + 11*X^10 + 21*X^9 + 32*X^8 + 31*X^7 + 7*X^6
    + 31*X^5 + 32*X^4 + 21*X^3 + 11*X^2 + 26*X + 30
  let Rp : ℤ[X] := 8*X^14 + 30*X^11 - 4*X^10 + 15*X^9 + 6*X^8 + 26*X^7 + 5*X^6 + 2*X^5 + 21*X^4 + 11*X^3
    + 26*X^2 - 37*X + 67
  let QP : ℤ[X] := 2*X^14 - 4*X^13 - 3*X^12 - 2*X^10 - 4*X^9 - 4*X^8 + X^7 - 4*X^6 - 4*X^5 - 2*X^4
    - 3*X^2 - 4*X + 2
  let RP : ℤ[X] := 2*X^13 - 6*X^12 + 3*X^11 - 3*X^10 + X^9 - 5*X^8 + X^7 - 4*X^5 - 4*X^3 + 10*X^2 - 12*X + 1
  let C1 : ℤ[X] := -X^13 - 13*X^12 - 169*X^11 - 2184*X^10 - 28224*X^9 - 364728*X^8 - 4713241*X^7
    - 60907405*X^6 - 787083025*X^5 - 10171171920*X^4 - 131438151935*X^3 - 1698524803236*X^2
    - 21949384290134*X - 283643470968507
  let C2 : ℤ[X] := -54707697586574*X + 4233484641321
  let d := 2
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
    have hn : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
    fin_cases hn <;> decide +revert
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_101 [Fact (Nat.Prime 101)]
    (hpn : 101 ≠ 17) : SeventeenCertificate 101 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X^2 - 4*X + 1
  let Q : ℤ[X] := X^14 + 5*X^13 + 20*X^12 + 76*X^11 + 285*X^10 + 1065*X^9 + 3976*X^8 + 14840*X^7
    + 55385*X^6 + 206701*X^5 + 771420*X^4 + 2878980*X^3 + 10744501*X^2 + 40099025*X + 149651600
  let A : ℤ[X] := 5529776*X - 1481699
  let G : ℤ[X] := -X^14 - X^13 - X^9 - X^8 - 2*X^5 - X^4 - X - 2
  let Qp : ℤ[X] := 11*X^15 + 11*X^14 - 44*X^12 - 7*X^11 - 17*X^10 + 7*X^9 + 12*X^8 + 8*X^7 - 13*X^6
    + 8*X^5 + 12*X^4 + 7*X^3 - 17*X^2 - 7*X - 44
  let Rp : ℤ[X] := 11*X^13 + 11*X^12 - 11*X^11 - 55*X^10 - 7*X^9 + 38*X^8 + 25*X^7 + 18*X^6 - 54*X^5
    - 10*X^4 + 38*X^3 + 17*X^2 - 71*X + 13
  let QP : ℤ[X] := 2*X^13 + X^11 + X^7 + X^3 + 2*X
  let RP : ℤ[X] := 2*X^11 - X^9 - X^7 + 2*X^6 + X^5 - X^4 - X^3 + 3*X^2 - X + 1
  let C1 : ℤ[X] := -X^12 - 5*X^11 - 19*X^10 - 71*X^9 - 265*X^8 - 990*X^7 - 3696*X^6 - 13794*X^5
    - 51480*X^4 - 192128*X^3 - 717033*X^2 - 2676004*X - 9986983
  let C2 : ℤ[X] := -369029*X + 98881
  let d := 2
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide +revert, fun n hnlt hnpos ↦ ?_⟩
    have hn : n ∈ Finset.Ioo 0 d := by simp [hnpos, hnlt]
    fin_cases hn <;> decide +revert
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_103 [Fact (Nat.Prime 103)]
    (hpn : 103 ≠ 17)
    (hmod : 103 % 17 = 1) : SeventeenCertificate 103 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 3
  let Q : ℤ[X] := X^15 - 2*X^14 + 7*X^13 - 20*X^12 + 61*X^11 - 182*X^10 + 547*X^9 - 1640*X^8 + 4921*X^7
    - 14762*X^6 + 44287*X^5 - 132860*X^4 + 398581*X^3 - 1195742*X^2 + 3587227*X - 10761680
  let A : ℤ[X] := 313447
  let G : ℤ[X] := X^10 + X^8 + 1
  let Qp : ℤ[X] := -8*X^15 + 16*X^14 + 47*X^13 + 57*X^12 + 27*X^11 + 14*X^10 + 53*X^9 + 39*X^8 + 81*X^7
    + 58*X^6 + 24*X^5 + 23*X^4 + 26*X^3 + 17*X^2 + 44*X + 66
  let Rp : ℤ[X] := 8*X^9 - 24*X^8 - 23*X^7 - 34*X^6 - X^5 + 3*X^4 - 9*X^3 + 27*X^2 - 81*X + 37
  let QP : ℤ[X] := X^14 + 2*X^13 + 2*X^12 + X^11 + X^10 + 2*X^9 + 2*X^8 + 3*X^7 + 2*X^6 + X^5 + X^4
    + X^3 + X^2 + 2*X + 2
  let RP : ℤ[X] := -X^8 - X^7 - X^6 - 2*X + 1
  let C1 : ℤ[X] := X^9 - 3*X^8 + 10*X^7 - 30*X^6 + 90*X^5 - 270*X^4 + 810*X^3 - 2430*X^2 + 7290*X - 21870
  let C2 : ℤ[X] := 637
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_137 [Fact (Nat.Prime 137)]
    (hpn : 137 ≠ 17)
    (hmod : 137 % 17 = 1) : SeventeenCertificate 137 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 4
  let Q : ℤ[X] := X^15 - 3*X^14 + 13*X^13 - 51*X^12 + 205*X^11 - 819*X^10 + 3277*X^9 - 13107*X^8
    + 52429*X^7 - 209715*X^6 + 838861*X^5 - 3355443*X^4 + 13421773*X^3 - 53687091*X^2 + 214748365*X
    - 858993459
  let A : ℤ[X] := 25080101
  let G : ℤ[X] := X^13 + X^11 + X^10 + X^7 + X^6 + X^5 + X^4 + X^3 + 1
  let Qp : ℤ[X] := -29*X^15 + 87*X^14 + 171*X^13 + 109*X^12 - 54*X^11 + 50*X^10 + 182*X^9 + 65*X^8
    - 15*X^7 + 31*X^6 + 121*X^5 + 172*X^4 - 32*X^3 - 38*X^2 + 123*X + 164
  let Rp : ℤ[X] := 29*X^12 - 116*X^11 - 55*X^10 - 25*X^9 - 37*X^8 - 126*X^7 + 122*X^6 + 89*X^5 - 327*X^4
    - 170*X^3 + 161*X^2 - 96*X - 27
  let QP : ℤ[X] := 4*X^14 + 6*X^13 + 3*X^12 - X^11 + 3*X^10 + 6*X^9 + 2*X^8 + 2*X^6 + 5*X^5 + 5*X^4
    - X^3 + 5*X + 5
  let RP : ℤ[X] := -4*X^11 - 2*X^10 - X^9 - 2*X^8 - 3*X^7 + 4*X^6 - 11*X^4 - 4*X^3 + 4*X^2 - 3*X - 1
  let C1 : ℤ[X] := X^12 - 4*X^11 + 17*X^10 - 67*X^9 + 268*X^8 - 1072*X^7 + 4289*X^6 - 17155*X^5
    + 68621*X^4 - 274483*X^3 + 1097933*X^2 - 4391732*X + 17566928
  let C2 : ℤ[X] := -512903
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_239 [Fact (Nat.Prime 239)]
    (hpn : 239 ≠ 17)
    (hmod : 239 % 17 = 1) : SeventeenCertificate 239 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 23
  let Q : ℤ[X] := X^15 - 22*X^14 + 507*X^13 - 11660*X^12 + 268181*X^11 - 6168162*X^10 + 141867727*X^9
    - 3262957720*X^8 + 75048027561*X^7 - 1726104633902*X^6 + 39700406579747*X^5 - 913109351334180*X^4
    + 21001515080686141*X^3 - 483034846855781242*X^2 + 11109801477682968567*X - 255525433986708277040
  let A : ℤ[X] := 24590313730938453439
  let G : ℤ[X] := X^3 + X + 1
  let Qp : ℤ[X] := -161*X^15 - 43*X^14 - 128*X^13 - 85*X^12 - 118*X^11 - 76*X^10 - 86*X^9 - 95*X^8
    - 127*X^7 - 108*X^6 - 67*X^5 - 54*X^4 - 114*X^3 - 168*X^2 - 121*X - 7
  let Rp : ℤ[X] := 161*X^2 - 118*X + 246
  let QP : ℤ[X] := -15*X^15 - 4*X^14 - 12*X^13 - 8*X^12 - 11*X^11 - 7*X^10 - 8*X^9 - 9*X^8 - 12*X^7
    - 10*X^6 - 6*X^5 - 5*X^4 - 11*X^3 - 16*X^2 - 11*X
  let RP : ℤ[X] := 15*X^2 - 11*X + 23
  let C1 : ℤ[X] := X^2 - 23*X + 530
  let C2 : ℤ[X] := -51
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_307 [Fact (Nat.Prime 307)]
    (hpn : 307 ≠ 17)
    (hmod : 307 % 17 = 1) : SeventeenCertificate 307 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 3
  let Q : ℤ[X] := X^15 - 2*X^14 + 7*X^13 - 20*X^12 + 61*X^11 - 182*X^10 + 547*X^9 - 1640*X^8 + 4921*X^7
    - 14762*X^6 + 44287*X^5 - 132860*X^4 + 398581*X^3 - 1195742*X^2 + 3587227*X - 10761680
  let A : ℤ[X] := 105163
  let G : ℤ[X] := X^8 - X^6 + 1
  let Qp : ℤ[X] := 140*X^15 + 27*X^14 + 59*X^13 - 37*X^12 - 56*X^11 + X^10 + 137*X^9 + 36*X^8 + 32*X^7
    + 44*X^6 + 8*X^5 + 116*X^4 + 99*X^3 + 150*X^2 - 3*X + 149
  let Rp : ℤ[X] := -140*X^7 + 113*X^6 + 108*X^5 - 17*X^4 + 51*X^3 - 153*X^2 - 155*X + 158
  let QP : ℤ[X] := X^15 - X^12 - X^11 + X^9 + X^4 + X^3 + X^2 + 1
  let RP : ℤ[X] := -X^7 + X^6 + X^5 - 2*X^2 - X + 2
  let C1 : ℤ[X] := X^7 - 3*X^6 + 8*X^5 - 24*X^4 + 72*X^3 - 216*X^2 + 648*X - 1944
  let C2 : ℤ[X] := 19
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_409 [Fact (Nat.Prime 409)]
    (hpn : 409 ≠ 17)
    (hmod : 409 % 17 = 1) : SeventeenCertificate 409 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 64
  let Q : ℤ[X] := X^15 - 63*X^14 + 4033*X^13 - 258111*X^12 + 16519105*X^11 - 1057222719*X^10
    + 67662254017*X^9 - 4330384257087*X^8 + 277144592453569*X^7 - 17737253917028415*X^6
    + 1135184250689818561*X^5 - 72651792044148387903*X^4 + 4649714690825496825793*X^3
    - 297581740212831796850751*X^2 + 19045231373621234998448065*X - 1218894807911759039900676159
  let A : ℤ[X] := 190731705883502637050472553
  let G : ℤ[X] := X^11 - X^7 - X^2 - 1
  let Qp : ℤ[X] := 26*X^15 - 2*X^14 - 255*X^13 - 14*X^12 + 104*X^11 - 86*X^10 - 196*X^9 - 109*X^8
    + 49*X^7 + 162*X^6 - 117*X^5 - 257*X^4 + 114*X^3 + 92*X^2 - 136*X - 268
  let Rp : ℤ[X] := -26*X^10 + 28*X^9 + 253*X^8 - 241*X^7 - 92*X^6 + 162*X^5 - 143*X^4 + 154*X^3 - 40*X^2
    - 277*X + 141
  let QP : ℤ[X] := 4*X^15 - X^14 - 40*X^13 - 2*X^12 + 16*X^11 - 14*X^10 - 31*X^9 - 17*X^8 + 8*X^7
    + 25*X^6 - 19*X^5 - 40*X^4 + 18*X^3 + 14*X^2 - 22*X - 42
  let RP : ℤ[X] := -4*X^10 + 5*X^9 + 39*X^8 - 38*X^7 - 14*X^6 + 25*X^5 - 22*X^4 + 24*X^3 - 7*X^2 - 43*X + 22
  let C1 : ℤ[X] := X^10 - 64*X^9 + 4096*X^8 - 262144*X^7 + 16777215*X^6 - 1073741760*X^5
    + 68719472640*X^4 - 4398046248960*X^3 + 281474959933440*X^2 - 18014397435740161*X
    + 1152921435887370304
  let C2 : ℤ[X] := -180408244246434473
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_443 [Fact (Nat.Prime 443)]
    (hpn : 443 ≠ 17)
    (hmod : 443 % 17 = 1) : SeventeenCertificate 443 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 15
  let Q : ℤ[X] := X^15 - 14*X^14 + 211*X^13 - 3164*X^12 + 47461*X^11 - 711914*X^10 + 10678711*X^9
    - 160180664*X^8 + 2402709961*X^7 - 36040649414*X^6 + 540609741211*X^5 - 8109146118164*X^4
    + 121637191772461*X^3 - 1824557876586914*X^2 + 27368368148803711*X - 410525522232055664
  let A : ℤ[X] := 13900412716661027
  let G : ℤ[X] := X^15 + X^14 - X^13 + X^11 + X^10 + X^7 + X^6 + X^2
  let Qp : ℤ[X] := 26*X^15 + 79*X^14 + 170*X^13 + 134*X^12 + 231*X^11 + 105*X^10 + 223*X^9 + 225*X^8
    + 195*X^7 + 202*X^6 + 97*X^5 - 100*X^4 + 197*X^3 + 172*X^2 + 104*X + 238
  let Rp : ℤ[X] := -26*X^14 - 79*X^13 - 118*X^12 - 2*X^11 + 4*X^10 - 86*X^9 - 39*X^8 - 301*X^7 + 59*X^6
    - 25*X^5 - 68*X^4 + 134*X^3 - 238*X^2 - 443*X + 443
  let QP : ℤ[X] := X^15 + 3*X^14 + 6*X^13 + 5*X^12 + 8*X^11 + 4*X^10 + 8*X^9 + 8*X^8 + 7*X^7 + 7*X^6
    + 3*X^5 - 3*X^4 + 7*X^3 + 6*X^2 + 4*X + 8
  let RP : ℤ[X] := -X^14 - 3*X^13 - 4*X^12 - 3*X^9 - 2*X^8 - 10*X^7 + 2*X^6 - X^5 - 2*X^4 + 4*X^3
    - 9*X^2 - 14*X + 15
  let C1 : ℤ[X] := X^14 - 14*X^13 + 209*X^12 - 3135*X^11 + 47026*X^10 - 705389*X^9 + 10580835*X^8
    - 158712525*X^7 + 2380687876*X^6 - 35710318139*X^5 + 535654772085*X^4 - 8034821581275*X^3
    + 120522323719125*X^2 - 1807834855786874*X + 27117522836803110
  let C2 : ℤ[X] := -918200547521550
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_613 [Fact (Nat.Prime 613)]
    (hpn : 613 ≠ 17)
    (hmod : 613 % 17 = 1) : SeventeenCertificate 613 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 27
  let Q : ℤ[X] := X^15 - 26*X^14 + 703*X^13 - 18980*X^12 + 512461*X^11 - 13836446*X^10 + 373584043*X^9
    - 10086769160*X^8 + 272342767321*X^7 - 7353254717666*X^6 + 198537877376983*X^5
    - 5360522689178540*X^4 + 144734112607820581*X^3 - 3907821040411155686*X^2 + 105511168091101203523*X
    - 2848801538459732495120
  let A : ℤ[X] := 125477392395453144157
  let G : ℤ[X] := X^6 - X^5 - 1
  let Qp : ℤ[X] := 111*X^15 + 179*X^14 + 182*X^13 + 101*X^12 + 449*X^11 + 248*X^10 + 158*X^9 + 136*X^8
    + 117*X^7 + 17*X^6 + 265*X^5 + 312*X^4 + 269*X^3 + 204*X^2 + 120*X - 64
  let Rp : ℤ[X] := -111*X^5 + 43*X^4 + 65*X^3 + 84*X^2 - 429*X + 549
  let QP : ℤ[X] := 5*X^15 + 8*X^14 + 8*X^13 + 5*X^12 + 20*X^11 + 11*X^10 + 7*X^9 + 6*X^8 + 5*X^7 + X^6
    + 12*X^5 + 14*X^4 + 12*X^3 + 9*X^2 + 5*X - 3
  let RP : ℤ[X] := -5*X^5 + 2*X^4 + 3*X^3 + 3*X^2 - 18*X + 24
  let C1 : ℤ[X] := X^5 - 28*X^4 + 756*X^3 - 20412*X^2 + 551124*X - 14880348
  let C2 : ℤ[X] := 655415
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact SeventeenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [cyclotomic_17]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [cyclotomic_17]
    refine ⟨?_, ?_, ?_⟩ <;> ring
