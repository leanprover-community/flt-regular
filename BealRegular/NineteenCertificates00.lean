import BealRegular.NineteenCertificateBase

/-! Exact polynomial certificates for p = 19, rational primes 7 through 7297. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_7 [Fact (Nat.Prime 7)]
    (hpn : 7 ≠ 19) :
    NineteenCertificate 7 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X^3 + 2*X - 1
  let Q : ℤ[X] := X^15 + X^14 - X^13 + 4*X^11 - 7*X^9 + 5*X^8 + 15*X^7 - 16*X^6 - 24*X^5 + 48*X^4
    + 33*X^3 - 119*X^2 - 17*X + 272
  let A : ℤ[X] := -12*X^2 - 80*X + 39
  let G : ℤ[X] := X^10 + X^6 + 1
  let Qp : ℤ[X] := 2*X^16 - X^15 + 2*X^14 + 3*X^13 + X^12 + 2*X^11 + 3*X^9 + X^8 - X^4 - X^3 + X^2 + 3
  let Rp : ℤ[X] := -2*X^8 + 3*X^7 - 3*X^6 - X^5 + 2*X^3 - X^2 - 4*X + 4
  let QP : ℤ[X] := X^17 + X^15 + X^14 + X^12 + X^10 + X^3 + X
  let RP : ℤ[X] := -X^9 + X^8 - X^7 - X^2 + 2*X - 1
  let C1 : ℤ[X] := X^7 - 2*X^5 + X^4 + 5*X^3 - 4*X^2 - 9*X + 13
  let C2 : ℤ[X] := 2*X^2 - 5*X + 2
  let d := 3
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
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_11 [Fact (Nat.Prime 11)]
    (hpn : 11 ≠ 19) :
    NineteenCertificate 11 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X^3 + X^2 + 2*X - 1
  let Q : ℤ[X] := X^15 - X^13 + 3*X^12 - 6*X^10 + 10*X^9 + 3*X^8 - 28*X^7 + 33*X^6 + 27*X^5 - 120*X^4
    + 100*X^3 + 168*X^2 - 487*X + 252
  let A : ℤ[X] := 81*X^2 - 90*X + 23
  let G : ℤ[X] := X^11 + X^7 + X + 1
  let Qp : ℤ[X] := -X^17 - X^16 - X^15 - 2*X^14 - X^13 - 4*X^11 - X^10 - 6*X^9 - 4*X^7 - 6*X^6 - X^5
    - 6*X^4 - 2*X^3 - 2*X^2 - 4*X + 2
  let Rp : ℤ[X] := X^10 + X^7 - X^5 + 4*X^4 - 2*X^3 + 4*X^2 - 7*X + 9
  let QP : ℤ[X] := -X^12 - X^10 - X^8 - X^7 - X^5 + X
  let RP : ℤ[X] := X^5 - X^4 + X^3 - X^2 + 2*X - 1
  let C1 : ℤ[X] := X^8 - X^7 - X^6 + 4*X^5 - 2*X^4 - 7*X^3 + 15*X^2 - 3*X - 34
  let C2 : ℤ[X] := 5*X^2 + 6*X - 3
  let d := 3
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
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_37 [Fact (Nat.Prime 37)]
    (hpn : 37 ≠ 19) :
    NineteenCertificate 37 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X^2 - 7*X + 1
  let Q : ℤ[X] := X^16 + 8*X^15 + 56*X^14 + 385*X^13 + 2640*X^12 + 18096*X^11 + 124033*X^10 + 850136*X^9
    + 5826920*X^8 + 39938305*X^7 + 273741216*X^6 + 1876250208*X^5 + 12860010241*X^4 + 88143821480*X^3
    + 604146740120*X^2 + 4140883359361*X + 28382036775408
  let A : ℤ[X] := 5257658758608*X - 767082075011
  let G : ℤ[X] := X^6 + X^5 + X^3 + X + 1
  let Qp : ℤ[X] := -18*X^17 - 11*X^16 - 18*X^15 - 15*X^13 - 27*X^12 - 22*X^11 - 12*X^10 - 21*X^9
    - 20*X^8 - 4*X^7 - 4*X^6 - 20*X^5 - 21*X^4 - 12*X^3 - 22*X^2 - 27*X - 15
  let Rp : ℤ[X] := 18*X^5 + 11*X^4 + 7*X^2 - 10*X + 52
  let QP : ℤ[X] := -2*X^17 - 4*X^15 - X^14 + X^13 - 2*X^11 - 3*X^8 - 3*X^7 - 2*X^4 + X^2 - X - 4
  let RP : ℤ[X] := 2*X^5 + 2*X^3 + 3*X^2 - 7*X + 5
  let C1 : ℤ[X] := X^4 + 8*X^3 + 55*X^2 + 378*X + 2591
  let C2 : ℤ[X] := 480*X - 70
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
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_113 [Fact (Nat.Prime 113)]
    (hpn : 113 ≠ 19) :
    NineteenCertificate 113 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X^2 - 7*X + 1
  let Q : ℤ[X] := X^16 + 8*X^15 + 56*X^14 + 385*X^13 + 2640*X^12 + 18096*X^11 + 124033*X^10 + 850136*X^9
    + 5826920*X^8 + 39938305*X^7 + 273741216*X^6 + 1876250208*X^5 + 12860010241*X^4 + 88143821480*X^3
    + 604146740120*X^2 + 4140883359361*X + 28382036775408
  let A : ℤ[X] := 1721534283792*X - 251168467039
  let G : ℤ[X] := X^13 + X^12 + X^11 + X^9 + X^8 + X^5 + X^4 + X^2 + X + 1
  let Qp : ℤ[X] := 37*X^17 - 2*X^16 + 27*X^15 + 43*X^14 + 13*X^13 + 13*X^12 + 43*X^11 + 27*X^10 - 2*X^9
    + 37*X^8 + 41*X^6 + 26*X^5 - 7*X^4 + 3*X^3 - 7*X^2 + 26*X + 41
  let Rp : ℤ[X] := -37*X^12 + 2*X^11 - 27*X^10 - 6*X^9 - 52*X^8 + 16*X^7 + 10*X^6 - 59*X^5 - 8*X^4
    + 38*X^3 + 7*X^2 - 139*X + 72
  let QP : ℤ[X] := 3*X^17 + X^16 + 2*X^14 + 2*X^13 + X^11 + 3*X^10 + 3*X^8 + X^6 + 3*X^5 + 2*X^4 + 3*X^3
    + X^2 + 3
  let RP : ℤ[X] := -3*X^12 - X^11 + X^9 - 4*X^8 - X^7 + 4*X^6 - 2*X^5 - 5*X^4 - X^3 + 7*X^2 - 8*X - 2
  let C1 : ℤ[X] := X^11 + 8*X^10 + 56*X^9 + 384*X^8 + 2633*X^7 + 18048*X^6 + 123703*X^5 + 847873*X^4
    + 5811409*X^3 + 39831991*X^2 + 273012528*X + 1871255706
  let C2 : ℤ[X] := 113502455*X - 16559785
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
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_151 [Fact (Nat.Prime 151)]
    (hpn : 151 ≠ 19) :
    NineteenCertificate 151 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X^2 - 8*X + 1
  let Q : ℤ[X] := X^16 + 9*X^15 + 72*X^14 + 568*X^13 + 4473*X^12 + 35217*X^11 + 277264*X^10
    + 2182896*X^9 + 17185905*X^8 + 135304345*X^7 + 1065248856*X^6 + 8386686504*X^5 + 66028243177*X^4
    + 519839258913*X^3 + 4092685828128*X^2 + 32221647366112*X + 253680493100769
  let A : ℤ[X] := 13226637731391*X - 1680003265568
  let G : ℤ[X] := X^17 + X^15 + X^13 + X^11 + X^10 + X^9 + X^8 + X^6 + X^5 + X^3 + X^2 + X + 1
  let Qp : ℤ[X] := 36*X^17 + 15*X^16 - 38*X^15 + 12*X^14 + 12*X^13 - 38*X^12 + 15*X^11 + 36*X^10 - 7*X^8
    - 27*X^7 - 29*X^6 - 25*X^5 + 9*X^4 - 25*X^3 - 29*X^2 - 27*X - 7
  let Rp : ℤ[X] := -36*X^16 + 21*X^15 + 17*X^14 - 29*X^13 + 17*X^12 + 21*X^11 - 36*X^10 - 36*X^9
    + 21*X^8 + 24*X^7 + 27*X^6 + 5*X^5 - 16*X^4 + 25*X^3 + 29*X^2 - 124*X + 158
  let QP : ℤ[X] := X^17 + 4*X^16 + X^15 + X^14 + 4*X^13 + X^12 + 2*X^10 + 2*X^9 + 3*X^8 + 3*X^7 + 3*X^6
    + X^5 + 3*X^4 + 3*X^3 + 3*X^2 + 2*X + 2
  let RP : ℤ[X] := -X^16 - 3*X^15 + 2*X^14 - 3*X^13 - X^12 - 3*X^9 - 3*X^8 - X^7 - 2*X^6 - X^5 - X^4
    - 4*X^3 + 6*X^2 - 11*X - 1
  let C1 : ℤ[X] := X^15 + 8*X^14 + 64*X^13 + 504*X^12 + 3969*X^11 + 31248*X^10 + 246016*X^9
    + 1936881*X^8 + 15249033*X^7 + 120055384*X^6 + 945194039*X^5 + 7441496929*X^4 + 58586781394*X^3
    + 461252754223*X^2 + 3631435252391*X + 28590229264906
  let C2 : ℤ[X] := 1490664893158*X - 189339266655
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
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_191 [Fact (Nat.Prime 191)]
    (hpn : 191 ≠ 19)
    (hmod : 191 % 19 = 1) :
    NineteenCertificate 191 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 11
  let Q : ℤ[X] := X^17 - 10*X^16 + 111*X^15 - 1220*X^14 + 13421*X^13 - 147630*X^12 + 1623931*X^11
    - 17863240*X^10 + 196495641*X^9 - 2161452050*X^8 + 23775972551*X^7 - 261535698060*X^6
    + 2876892678661*X^5 - 31645819465270*X^4 + 348104014117971*X^3 - 3829144155297680*X^2
    + 42120585708274481*X - 463326442791019290
  let A : ℤ[X] := 26683721836132001
  let G : ℤ[X] := -X^16 - X^15 - X^12 - X^9 - X^8 - X^5 - X^4 - X
  let Qp : ℤ[X] := 93*X^17 + 25*X^16 + 9*X^15 - 6*X^14 - 32*X^13 + 63*X^12 - 27*X^11 + 8*X^10 + 5*X^9
    + 38*X^8 + 57*X^7 + 39*X^6 + 46*X^5 - 31*X^4 + 52*X^3 + 94*X^2 + 14*X + 130
  let Rp : ℤ[X] := 93*X^15 + 25*X^14 - 84*X^13 - 31*X^12 + 52*X^11 + X^10 - 11*X^9 + 23*X^8 + 31*X^7
    + 41*X^6 - 69*X^5 + 88*X^4 + 80*X^3 - 116*X^2 - 61*X + 191
  let QP : ℤ[X] := 5*X^17 + X^16 - X^14 - 2*X^13 + 3*X^12 - 2*X^11 + 2*X^8 + 3*X^7 + 2*X^6 + 2*X^5
    - 2*X^4 + 3*X^3 + 5*X^2 + X + 7
  let RP : ℤ[X] := 5*X^15 + X^14 - 5*X^13 - 2*X^12 + 3*X^11 - X^9 + X^8 + 2*X^7 + 2*X^6 - 4*X^5 + 5*X^4
    + 4*X^3 - 7*X^2 - 3*X + 11
  let C1 : ℤ[X] := -X^15 + 10*X^14 - 110*X^13 + 1210*X^12 - 13311*X^11 + 146421*X^10 - 1610631*X^9
    + 17716940*X^8 - 194886341*X^7 + 2143749751*X^6 - 23581247261*X^5 + 259393719870*X^4
    - 2853330918571*X^3 + 31386640104281*X^2 - 345253041147091*X + 3797783452618000
  let C2 : ℤ[X] := -218720512978000
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_227 [Fact (Nat.Prime 227)]
    (hpn : 227 ≠ 19) :
    NineteenCertificate 227 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X^2 - 19*X + 1
  let Q : ℤ[X] := X^16 + 20*X^15 + 380*X^14 + 7201*X^13 + 136440*X^12 + 2585160*X^11 + 48981601*X^10
    + 928065260*X^9 + 17584258340*X^8 + 333172843201*X^7 + 6312699762480*X^6 + 119608122643920*X^5
    + 2266241630472001*X^4 + 42938982856324100*X^3 + 813574432639685900*X^2 + 15414975237297708001*X
    + 292070955076016766120
  let A : ℤ[X] := 24378560225581589640*X - 1286656189762188397
  let G : ℤ[X] := X^14 + X^13 + X^11 + X^10 + X^8 + X^7 + X^6 + X^4 + X^3 + X + 1
  let Qp : ℤ[X] := -25*X^17 - 12*X^16 + 33*X^15 - 33*X^14 + 30*X^13 - 69*X^12 + 30*X^11 - 33*X^10
    + 33*X^9 - 12*X^8 - 25*X^7 + 34*X^5 - 26*X^4 - 65*X^3 - 65*X^2 - 26*X + 34
  let Rp : ℤ[X] := 25*X^13 + 12*X^12 - 58*X^11 + 46*X^10 + 15*X^9 - 22*X^8 + 46*X^7 - 21*X^6 - 13*X^4
    + 5*X^3 + 99*X^2 - 201*X + 193
  let QP : ℤ[X] := -X^17 - 5*X^16 + X^15 - 5*X^14 + 4*X^13 - 5*X^12 + X^11 - 5*X^10 - X^9 - 2*X^7
    - 5*X^6 + 3*X^4 + 3*X^3 - 5*X - 2
  let RP : ℤ[X] := X^13 + 5*X^12 - 2*X^11 + X^10 + 2*X^9 - 2*X^8 + 4*X^7 + 2*X^6 + X^5 + 2*X^4 - 7*X^3
    + 18*X^2 - 15*X + 3
  let C1 : ℤ[X] := X^12 + 20*X^11 + 379*X^10 + 7182*X^9 + 136080*X^8 + 2578338*X^7 + 48852343*X^6
    + 925616180*X^5 + 17537855078*X^4 + 332293630302*X^3 + 6296041120661*X^2 + 119292487662258*X
    + 2260261224462241
  let C2 : ℤ[X] := 188659342630486*X - 9957097905120
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
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_229 [Fact (Nat.Prime 229)]
    (hpn : 229 ≠ 19)
    (hmod : 229 % 19 = 1) :
    NineteenCertificate 229 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 4
  let Q : ℤ[X] := X^17 - 3*X^16 + 13*X^15 - 51*X^14 + 205*X^13 - 819*X^12 + 3277*X^11 - 13107*X^10
    + 52429*X^9 - 209715*X^8 + 838861*X^7 - 3355443*X^6 + 13421773*X^5 - 53687091*X^4 + 214748365*X^3
    - 858993459*X^2 + 3435973837*X - 13743895347
  let A : ℤ[X] := 240068041
  let G : ℤ[X] := -X^17 - X^16 - X^13 - X^12 - X^9 - X^5 - X^4 - X^2 - X
  let Qp : ℤ[X] := -5*X^17 + 15*X^16 - 65*X^15 + 26*X^14 + 120*X^13 - 27*X^12 + 103*X^11 + 41*X^10
    + 60*X^9 - 16*X^8 + 59*X^7 - 12*X^6 + 43*X^5 + 52*X^4 + 16*X^3 - 69*X^2 + 42*X + 56
  let Rp : ℤ[X] := -5*X^16 + 15*X^15 - 60*X^14 + 11*X^13 + 180*X^12 - 38*X^11 - 77*X^10 + 79*X^9
    + 137*X^8 - 90*X^7 - 98*X^6 + 163*X^5 + 30*X^4 - 125*X^3 + 42*X^2 - 173*X + 229
  let QP : ℤ[X] := -X^15 + X^14 + 2*X^13 + 2*X^11 + X^10 + X^9 + X^7 + X^5 + X^4 - X^2 + X + 1
  let RP : ℤ[X] := -X^14 + X^13 + 3*X^12 - X^11 - X^10 + 2*X^9 + 2*X^8 - 2*X^7 - X^6 + 3*X^5 - 2*X^3 - 2*X + 4
  let C1 : ℤ[X] := -X^16 + 3*X^15 - 12*X^14 + 48*X^13 - 193*X^12 + 771*X^11 - 3084*X^10 + 12336*X^9
    - 49345*X^8 + 197380*X^7 - 789520*X^6 + 3158080*X^5 - 12632321*X^4 + 50529283*X^3 - 202117132*X^2
    + 808468527*X - 3233874109
  let C2 : ℤ[X] := 56486884
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_419 [Fact (Nat.Prime 419)]
    (hpn : 419 ≠ 19)
    (hmod : 419 % 19 = 1) :
    NineteenCertificate 419 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 40
  let Q : ℤ[X] := X^17 - 39*X^16 + 1561*X^15 - 62439*X^14 + 2497561*X^13 - 99902439*X^12
    + 3996097561*X^11 - 159843902439*X^10 + 6393756097561*X^9 - 255750243902439*X^8
    + 10230009756097561*X^7 - 409200390243902439*X^6 + 16368015609756097561*X^5
    - 654720624390243902439*X^4 + 26188824975609756097561*X^3 - 1047552999024390243902439*X^2
    + 41902119960975609756097561*X - 1676084798439024390243902439
  let A : ℤ[X] := 160008095316374643460038419
  let G : ℤ[X] := X^10 - X^4 - 1
  let Qp : ℤ[X] := 100*X^17 - 129*X^16 - 187*X^15 + 38*X^14 - 163*X^13 - 84*X^12 + 108*X^11 - 30*X^10
    + 43*X^9 + 56*X^8 - 45*X^7 - 195*X^6 - 61*X^5 + 26*X^4 - 102*X^3 - 10*X^2 + 81*X - 207
  let Rp : ℤ[X] := -100*X^9 + 229*X^8 + 58*X^7 - 225*X^6 + 201*X^5 - 79*X^4 - 92*X^3 - 91*X^2 - 131*X + 212
  let QP : ℤ[X] := 9*X^17 - 13*X^16 - 18*X^15 + 3*X^14 - 16*X^13 - 8*X^12 + 10*X^11 - 3*X^10 + 4*X^9
    + 5*X^8 - 5*X^7 - 19*X^6 - 6*X^5 + 2*X^4 - 10*X^3 - X^2 + 7*X - 20
  let RP : ℤ[X] := -9*X^9 + 22*X^8 + 5*X^7 - 21*X^6 + 19*X^5 - 8*X^4 - 9*X^3 - 9*X^2 - 12*X + 20
  let C1 : ℤ[X] := X^9 - 40*X^8 + 1600*X^7 - 64000*X^6 + 2560000*X^5 - 102400000*X^4 + 4095999999*X^3
    - 163839999960*X^2 + 6553599998400*X - 262143999936000
  let C2 : ℤ[X] := 25025680184821
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_457 [Fact (Nat.Prime 457)]
    (hpn : 457 ≠ 19)
    (hmod : 457 % 19 = 1) :
    NineteenCertificate 457 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 4
  let Q : ℤ[X] := X^17 - 3*X^16 + 13*X^15 - 51*X^14 + 205*X^13 - 819*X^12 + 3277*X^11 - 13107*X^10
    + 52429*X^9 - 209715*X^8 + 838861*X^7 - 3355443*X^6 + 13421773*X^5 - 53687091*X^4 + 214748365*X^3
    - 858993459*X^2 + 3435973837*X - 13743895347
  let A : ℤ[X] := 120296677
  let G : ℤ[X] := X^6 + X^2 + 1
  let Qp : ℤ[X] := 163*X^17 - 32*X^16 - 166*X^15 - 87*X^14 + 54*X^13 - 53*X^12 - 82*X^11 + 34*X^10
    + 27*X^9 + 55*X^8 - 57*X^7 - 66*X^6 - 30*X^5 - 174*X^4 - 55*X^3 - 74*X^2 + 2*X + 155
  let Rp : ℤ[X] := -163*X^5 + 195*X^4 + 134*X^3 - 79*X^2 - 304*X + 302
  let QP : ℤ[X] := X^17 - X^16 - 2*X^15 - X^14 - X^12 - X^11 - X^7 - X^6 - X^5 - 2*X^4 - X^3 - X^2 + 1
  let RP : ℤ[X] := -X^5 + 2*X^4 + X^3 - X^2 - 2*X + 3
  let C1 : ℤ[X] := X^5 - 4*X^4 + 16*X^3 - 64*X^2 + 257*X - 1028
  let C2 : ℤ[X] := 9
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_571 [Fact (Nat.Prime 571)]
    (hpn : 571 ≠ 19)
    (hmod : 571 % 19 = 1) :
    NineteenCertificate 571 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 8
  let Q : ℤ[X] := X^17 - 7*X^16 + 57*X^15 - 455*X^14 + 3641*X^13 - 29127*X^12 + 233017*X^11
    - 1864135*X^10 + 14913081*X^9 - 119304647*X^8 + 954437177*X^7 - 7635497415*X^6 + 61083979321*X^5
    - 488671834567*X^4 + 3909374676537*X^3 - 31274997412295*X^2 + 250199979298361*X - 2001599834386887
  let A : ℤ[X] := 28043430254107
  let G : ℤ[X] := 2*X^17 + 2*X^16 + 2*X^13 + 2*X^12 + X^10 + 2*X^9 + 2*X^8 + X^6 + 2*X^5 + X^4 + X^2 + 2*X + 1
  let Qp : ℤ[X] := -28*X^17 + 196*X^16 + 117*X^15 + 178*X^14 + 261*X^13 + 168*X^12 + 341*X^11 + 99*X^10
    + 322*X^9 + 251*X^8 + 248*X^7 + 272*X^6 + 80*X^5 - 97*X^4 + 177*X^3 + 269*X^2 + 104*X + 282
  let Rp : ℤ[X] := 56*X^16 - 392*X^15 - 290*X^14 + 36*X^13 - 232*X^12 - 372*X^11 - 450*X^10 + 202*X^9
    - 418*X^8 - 597*X^7 - 363*X^6 + 77*X^5 + 11*X^4 - 60*X^3 - 91*X^2 - 957*X + 289
  let QP : ℤ[X] := 3*X^16 + 2*X^15 + 3*X^14 + 4*X^13 + 3*X^12 + 5*X^11 + 2*X^10 + 5*X^9 + 4*X^8 + 4*X^7
    + 4*X^6 + X^5 - X^4 + 3*X^3 + 4*X^2 + 2*X + 4
  let RP : ℤ[X] := -6*X^15 - 4*X^14 - 4*X^12 - 6*X^11 - 6*X^10 + 2*X^9 - 7*X^8 - 9*X^7 - 5*X^6 + X^5
    - X^3 - 3*X^2 - 13*X + 4
  let C1 : ℤ[X] := 2*X^16 - 14*X^15 + 112*X^14 - 896*X^13 + 7170*X^12 - 57358*X^11 + 458864*X^10
    - 3670911*X^9 + 29367290*X^8 - 234938318*X^7 + 1879506544*X^6 - 15036052351*X^5 + 120288418810*X^4
    - 962307350479*X^3 + 7698458803832*X^2 - 61587670430655*X + 492701363445242
  let C2 : ℤ[X] := -6902996335485
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_647 [Fact (Nat.Prime 647)]
    (hpn : 647 ≠ 19)
    (hmod : 647 % 19 = 1) :
    NineteenCertificate 647 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 99
  let Q : ℤ[X] := X^17 - 98*X^16 + 9703*X^15 - 960596*X^14 + 95099005*X^13 - 9414801494*X^12
    + 932065347907*X^11 - 92274469442792*X^10 + 9135172474836409*X^9 - 904382075008804490*X^8
    + 89533825425871644511*X^7 - 8863848717161292806588*X^6 + 877521022998967987852213*X^5
    - 86874581276897830797369086*X^4 + 8600583546412885248939539515*X^3
    - 851457771094875639645014411984*X^2 + 84294319338392688324856426786417*X
    - 8345137614500876144160786251855282
  let A : ℤ[X] := 1276922138849438544469733908707377
  let G : ℤ[X] := -X^6 - X^4 - X^3 - 1
  let Qp : ℤ[X] := 166*X^17 - 93*X^16 - 332*X^15 + 37*X^14 - 262*X^13 + 224*X^12 - 12*X^11 + 60*X^10
    + 49*X^9 - 156*X^8 + 82*X^7 - 188*X^6 + 15*X^5 - 25*X^4 + 53*X^3 + 95*X^2 - 181*X - 31
  let Rp : ℤ[X] := 166*X^5 - 259*X^4 - 73*X^3 + 276*X^2 - 797*X + 616
  let QP : ℤ[X] := 25*X^17 - 15*X^16 - 51*X^15 + 5*X^14 - 40*X^13 + 34*X^12 - 2*X^11 + 9*X^10 + 7*X^9
    - 24*X^8 + 12*X^7 - 29*X^6 + 2*X^5 - 4*X^4 + 8*X^3 + 14*X^2 - 28*X - 5
  let RP : ℤ[X] := 25*X^5 - 40*X^4 - 11*X^3 + 41*X^2 - 121*X + 94
  let C1 : ℤ[X] := -X^5 + 99*X^4 - 9802*X^3 + 970397*X^2 - 96069303*X + 9510860997
  let C2 : ℤ[X] := -1455294032
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_761 [Fact (Nat.Prime 761)]
    (hpn : 761 ≠ 19)
    (hmod : 761 % 19 = 1) :
    NineteenCertificate 761 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 5
  let Q : ℤ[X] := X^17 - 4*X^16 + 21*X^15 - 104*X^14 + 521*X^13 - 2604*X^12 + 13021*X^11 - 65104*X^10
    + 325521*X^9 - 1627604*X^8 + 8138021*X^7 - 40690104*X^6 + 203450521*X^5 - 1017252604*X^4
    + 5086263021*X^3 - 25431315104*X^2 + 127156575521*X - 635782877604
  let A : ℤ[X] := 4177285661
  let G : ℤ[X] := X^17 + 3*X^16 + 2*X^15 + X^13 + 3*X^12 + 2*X^11 + 2*X^9 + 3*X^8 + X^7 + 2*X^5 + 3*X^4
    + 3*X + 3
  let Qp : ℤ[X] := -102*X^17 - 353*X^16 + 141*X^15 - 46*X^14 + 128*X^13 + 19*X^12 - 197*X^11 + 122*X^10
    + 49*X^9 + 414*X^8 + 111*X^7 + 104*X^6 + 139*X^5 - 36*X^4 + 78*X^3 + 269*X^2 + 75*X + 284
  let Rp : ℤ[X] := 102*X^16 + 557*X^15 + 463*X^14 - 793*X^13 - 499*X^12 + 518*X^11 + 658*X^10 - 246*X^9
    - 849*X^8 - 15*X^7 - 584*X^6 - 124*X^5 + 63*X^4 - 9*X^3 + 45*X^2 - 986*X - 91
  let QP : ℤ[X] := -X^17 - 2*X^16 + X^15 + X^13 - X^11 + X^10 + X^9 + 3*X^8 + X^7 + X^6 + X^5 + X^3
    + 2*X^2 + X + 2
  let RP : ℤ[X] := X^16 + 4*X^15 + 2*X^14 - 6*X^13 - 3*X^12 + 4*X^11 + 4*X^10 - 3*X^9 - 6*X^8 - X^7
    - 4*X^6 - X^5 - X^2 - 7*X - 1
  let C1 : ℤ[X] := X^16 - 2*X^15 + 12*X^14 - 60*X^13 + 301*X^12 - 1502*X^11 + 7512*X^10 - 37560*X^9
    + 187802*X^8 - 939007*X^7 + 4695036*X^6 - 23475180*X^5 + 117375902*X^4 - 586879507*X^3
    + 2934397535*X^2 - 14671987675*X + 73359938378
  let C2 : ℤ[X] := -481996967
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_1103 [Fact (Nat.Prime 1103)]
    (hpn : 1103 ≠ 19)
    (hmod : 1103 % 19 = 1) :
    NineteenCertificate 1103 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 307
  let Q : ℤ[X] := X^17 - 306*X^16 + 93943*X^15 - 28840500*X^14 + 8854033501*X^13 - 2718188284806*X^12
    + 834483803435443*X^11 - 256186527654681000*X^10 + 78649263989987067001*X^9
    - 24145324044926029569306*X^8 + 7412614481792291077776943*X^7 - 2275672645910233360877521500*X^6
    + 698631502294441641789399100501*X^5 - 214479871204393584029345523853806*X^4
    + 65845320459748830297009075823118443*X^3 - 20214513381142890901181786277697362000*X^2
    + 6205855608010867506662808387253090134001*X - 1905197671659336324545482174886698671138306
  let A : ℤ[X] := 530277139800014734030338193735463728050281
  let G : ℤ[X] := X^10 + X^5 + X + 1
  let Qp : ℤ[X] := -507*X^17 - 381*X^16 - 458*X^15 + 18*X^14 - 518*X^13 - 313*X^12 - 377*X^11 - 583*X^10
    - 212*X^9 - 500*X^8 - 324*X^7 - 309*X^6 - 502*X^5 - 813*X^4 - 194*X^3 - 511*X^2 - 256*X - 228
  let Rp : ℤ[X] := 507*X^9 - 126*X^8 + 77*X^7 - 476*X^6 + 536*X^5 + 302*X^4 - 62*X^3 + 283*X^2 - 847*X + 1331
  let QP : ℤ[X] := -141*X^17 - 106*X^16 - 127*X^15 + 5*X^14 - 144*X^13 - 87*X^12 - 105*X^11 - 162*X^10
    - 59*X^9 - 139*X^8 - 90*X^7 - 86*X^6 - 140*X^5 - 226*X^4 - 54*X^3 - 142*X^2 - 71*X - 63
  let RP : ℤ[X] := 141*X^9 - 35*X^8 + 21*X^7 - 132*X^6 + 149*X^5 + 84*X^4 - 17*X^3 + 78*X^2 - 235*X + 370
  let C1 : ℤ[X] := X^9 - 307*X^8 + 94249*X^7 - 28934443*X^6 + 8882874001*X^5 - 2727042318306*X^4
    + 837201991719942*X^3 - 257021011458022194*X^2 + 78905450517612813558*X - 24223973308907133762305
  let C2 : ℤ[X] := 6742302634482765244812
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_1217 [Fact (Nat.Prime 1217)]
    (hpn : 1217 ≠ 19)
    (hmod : 1217 % 19 = 1) :
    NineteenCertificate 1217 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 16
  let Q : ℤ[X] := X^17 - 15*X^16 + 241*X^15 - 3855*X^14 + 61681*X^13 - 986895*X^12 + 15790321*X^11
    - 252645135*X^10 + 4042322161*X^9 - 64677154575*X^8 + 1034834473201*X^7 - 16557351571215*X^6
    + 264917625139441*X^5 - 4238682002231055*X^4 + 67818912035696881*X^3 - 1085102592571150095*X^2
    + 17361641481138401521*X - 277786263698214424335
  let A : ℤ[X] := 3652079062589507633
  let G : ℤ[X] := X^17 + X^16 + 2*X^13 + X^12 + X^10 + X^9 + X^8 + X^6 + 2*X^5 + X^4 + X^2 + 2*X
  let Qp : ℤ[X] := -602*X^17 - 706*X^16 - 259*X^15 - 109*X^14 - 75*X^13 - 619*X^12 - 434*X^11 - 960*X^10
    + 154*X^9 - 632*X^8 - 226*X^7 - 637*X^6 - 146*X^5 - 700*X^4 - 355*X^3 - 1007*X^2 - 311*X - 494
  let Rp : ℤ[X] := 602*X^16 + 706*X^15 - 343*X^14 - 597*X^13 + 1020*X^12 + 1320*X^11 - 431*X^10
    + 196*X^9 - 100*X^8 + 985*X^7 + 61*X^6 + 843*X^5 - 114*X^4 + 1209*X^3 + 128*X^2 - 229*X + 1217
  let QP : ℤ[X] := -8*X^17 - 9*X^16 - 3*X^15 - X^14 - X^13 - 8*X^12 - 6*X^11 - 12*X^10 + 2*X^9 - 8*X^8
    - 3*X^7 - 8*X^6 - 2*X^5 - 9*X^4 - 5*X^3 - 13*X^2 - 4*X - 6
  let RP : ℤ[X] := 8*X^16 + 9*X^15 - 5*X^14 - 8*X^13 + 14*X^12 + 17*X^11 - 6*X^10 + 2*X^9 - X^8 + 13*X^7
    + X^6 + 10*X^5 - X^4 + 16*X^3 + X^2 - 3*X + 16
  let C1 : ℤ[X] := X^16 - 15*X^15 + 240*X^14 - 3840*X^13 + 61442*X^12 - 983071*X^11 + 15729136*X^10
    - 251666175*X^9 + 4026658801*X^8 - 64426540815*X^7 + 1030824653040*X^6 - 16493194448639*X^5
    + 263891111178226*X^4 - 4222257778851615*X^3 + 67556124461625840*X^2 - 1080897991386013439*X
    + 17294367862176215026
  let C2 : ℤ[X] := -227370489560246048
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_1483 [Fact (Nat.Prime 1483)]
    (hpn : 1483 ≠ 19)
    (hmod : 1483 % 19 = 1) :
    NineteenCertificate 1483 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 45
  let Q : ℤ[X] := X^17 - 44*X^16 + 1981*X^15 - 89144*X^14 + 4011481*X^13 - 180516644*X^12
    + 8123248981*X^11 - 365546204144*X^10 + 16449579186481*X^9 - 740231063391644*X^8
    + 33310397852623981*X^7 - 1498967903368079144*X^6 + 67453555651563561481*X^5
    - 3035410004320360266644*X^4 + 136593450194416211998981*X^3 - 6146705258748729539954144*X^2
    + 276601736643692829297936481*X - 12447078148966177318407141644
  let A : ℤ[X] := 377692863589668226114849207
  let G : ℤ[X] := X^7 - X + 1
  let Qp : ℤ[X] := 457*X^17 + 654*X^16 + 687*X^15 + 685*X^14 + 775*X^13 + 1174*X^12 + 1015*X^11
    + 755*X^10 + 591*X^9 + 556*X^8 + 648*X^7 + 957*X^6 + 399*X^5 + 298*X^4 + 394*X^3 + 523*X^2 + 650*X
    + 867
  let Rp : ℤ[X] := -457*X^6 - 197*X^5 - 33*X^4 + 2*X^3 - 90*X^2 - 399*X + 616
  let QP : ℤ[X] := 14*X^17 + 20*X^16 + 21*X^15 + 21*X^14 + 24*X^13 + 36*X^12 + 31*X^11 + 23*X^10
    + 18*X^9 + 17*X^8 + 20*X^7 + 29*X^6 + 12*X^5 + 9*X^4 + 12*X^3 + 16*X^2 + 20*X + 26
  let RP : ℤ[X] := -14*X^6 - 6*X^5 - X^4 - 3*X^2 - 12*X + 19
  let C1 : ℤ[X] := X^6 - 45*X^5 + 2025*X^4 - 91125*X^3 + 4100625*X^2 - 184528125*X + 8303765624
  let C2 : ℤ[X] := -251968613
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_1559 [Fact (Nat.Prime 1559)]
    (hpn : 1559 ≠ 19)
    (hmod : 1559 % 19 = 1) :
    NineteenCertificate 1559 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 17
  let Q : ℤ[X] := X^17 - 16*X^16 + 273*X^15 - 4640*X^14 + 78881*X^13 - 1340976*X^12 + 22796593*X^11
    - 387542080*X^10 + 6588215361*X^9 - 111999661136*X^8 + 1903994239313*X^7 - 32367902068320*X^6
    + 550254335161441*X^5 - 9354323697744496*X^4 + 159023502861656433*X^3 - 2703399548648159360*X^2
    + 45957792327018709121*X - 781282469559318055056
  let A : ℤ[X] := 8519436807253628567
  let G : ℤ[X] := X^16 + X^10 + X^4 + 1
  let Qp : ℤ[X] := 120*X^17 - 361*X^16 + 21*X^15 - 237*X^14 - 528*X^13 - 258*X^12 - 171*X^11 - 91*X^10
    + 108*X^9 - 157*X^8 - 329*X^7 - 523*X^6 - 343*X^5 - 285*X^4 + 288*X^3 - 99*X^2 + 244*X + 649
  let Rp : ℤ[X] := -120*X^15 + 481*X^14 - 382*X^13 + 258*X^12 + 291*X^11 - 270*X^10 - 207*X^9 + 401*X^8
    - 581*X^7 + 523*X^6 + 463*X^5 - 76*X^4 - 387*X^3 + 343*X^2 - 1154*X + 910
  let QP : ℤ[X] := X^17 - 4*X^16 - 3*X^14 - 6*X^13 - 3*X^12 - 2*X^11 - X^10 + X^9 - 2*X^8 - 4*X^7
    - 6*X^6 - 4*X^5 - 3*X^4 + 3*X^3 - X^2 + 3*X + 7
  let RP : ℤ[X] := -X^15 + 5*X^14 - 4*X^13 + 3*X^12 + 3*X^11 - 3*X^10 - 2*X^9 + 4*X^8 - 6*X^7 + 6*X^6
    + 5*X^5 - X^4 - 4*X^3 + 3*X^2 - 12*X + 10
  let C1 : ℤ[X] := X^15 - 17*X^14 + 289*X^13 - 4913*X^12 + 83521*X^11 - 1419857*X^10 + 24137570*X^9
    - 410338690*X^8 + 6975757730*X^7 - 118587881410*X^6 + 2015993983970*X^5 - 34271897727490*X^4
    + 582622261367331*X^3 - 9904578443244627*X^2 + 168377833535158659*X - 2862423170097697203
  let C2 : ℤ[X] := 31213081392983228
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_1597 [Fact (Nat.Prime 1597)]
    (hpn : 1597 ≠ 19)
    (hmod : 1597 % 19 = 1) :
    NineteenCertificate 1597 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 40
  let Q : ℤ[X] := X^17 - 39*X^16 + 1561*X^15 - 62439*X^14 + 2497561*X^13 - 99902439*X^12
    + 3996097561*X^11 - 159843902439*X^10 + 6393756097561*X^9 - 255750243902439*X^8
    + 10230009756097561*X^7 - 409200390243902439*X^6 + 16368015609756097561*X^5
    - 654720624390243902439*X^4 + 26188824975609756097561*X^3 - 1047552999024390243902439*X^2
    + 41902119960975609756097561*X - 1676084798439024390243902439
  let A : ℤ[X] := 41980834024772057363654413
  let G : ℤ[X] := X^6 + X^4 + X^2 + X + 1
  let Qp : ℤ[X] := -833*X^17 - 1050*X^16 - 355*X^15 - 1006*X^14 - 518*X^13 - 874*X^12 - 1007*X^11
    - 478*X^10 - 877*X^9 - 887*X^8 - 487*X^7 - 517*X^6 - 914*X^5 - 1004*X^4 - 598*X^3 - 868*X^2 - 1247*X
    - 460
  let Rp : ℤ[X] := 833*X^5 + 217*X^4 + 138*X^3 + 868*X^2 - 350*X + 2057
  let QP : ℤ[X] := -21*X^17 - 26*X^16 - 9*X^15 - 25*X^14 - 13*X^13 - 22*X^12 - 25*X^11 - 12*X^10
    - 22*X^9 - 22*X^8 - 12*X^7 - 13*X^6 - 23*X^5 - 25*X^4 - 15*X^3 - 22*X^2 - 31*X - 11
  let RP : ℤ[X] := 21*X^5 + 5*X^4 + 4*X^3 + 21*X^2 - 8*X + 51
  let C1 : ℤ[X] := X^5 - 40*X^4 + 1601*X^3 - 64040*X^2 + 2561601*X - 102464039
  let C2 : ℤ[X] := 2566413
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_1787 [Fact (Nat.Prime 1787)]
    (hpn : 1787 ≠ 19)
    (hmod : 1787 % 19 = 1) :
    NineteenCertificate 1787 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 6
  let Q : ℤ[X] := X^17 - 5*X^16 + 31*X^15 - 185*X^14 + 1111*X^13 - 6665*X^12 + 39991*X^11 - 239945*X^10
    + 1439671*X^9 - 8638025*X^8 + 51828151*X^7 - 310968905*X^6 + 1865813431*X^5 - 11194880585*X^4
    + 67169283511*X^3 - 403015701065*X^2 + 2418094206391*X - 14508565238345
  let A : ℤ[X] := 48713705333
  let G : ℤ[X] := -X^16 - X^12 - X^8 + X^2
  let Qp : ℤ[X] := 514*X^17 - 783*X^16 - 149*X^15 - 379*X^14 - 786*X^13 - 131*X^12 - 487*X^11 - 138*X^10
    - 445*X^9 - 390*X^8 - 720*X^7 - 527*X^6 + 102*X^5 - 98*X^4 - 685*X^3 - 737*X^2 - 425*X - 510
  let Rp : ℤ[X] := 514*X^15 - 1297*X^14 + 634*X^13 - 230*X^12 + 107*X^11 - 642*X^10 + 278*X^9 + 119*X^8
    - 200*X^7 - 587*X^6 - 52*X^5 + 312*X^4 - 85*X^3 + 510*X^2 - 1787*X + 1787
  let QP : ℤ[X] := X^17 - 3*X^16 - X^15 - 2*X^14 - 3*X^13 - X^12 - 2*X^11 - X^10 - 2*X^9 - 2*X^8 - 3*X^7
    - 2*X^6 - X^4 - 3*X^3 - 3*X^2 - 2*X - 2
  let RP : ℤ[X] := X^15 - 4*X^14 + 2*X^13 - X^12 - 2*X^10 + X^9 - X^7 - 2*X^6 + X^4 + X^2 - 5*X + 6
  let C1 : ℤ[X] := -X^15 + 6*X^14 - 36*X^13 + 216*X^12 - 1297*X^11 + 7782*X^10 - 46692*X^9 + 280152*X^8
    - 1680913*X^7 + 10085478*X^6 - 60512868*X^5 + 363077208*X^4 - 2178463248*X^3 + 13070779488*X^2
    - 78424676927*X + 470548061562
  let C2 : ℤ[X] := -1579903956
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_1901 [Fact (Nat.Prime 1901)]
    (hpn : 1901 ≠ 19)
    (hmod : 1901 % 19 = 1) :
    NineteenCertificate 1901 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 214
  let Q : ℤ[X] := X^17 - 213*X^16 + 45583*X^15 - 9754761*X^14 + 2087518855*X^13 - 446729034969*X^12
    + 95600013483367*X^11 - 20458402885440537*X^10 + 4378098217484274919*X^9 - 936913018541634832665*X^8
    + 200499385967909854190311*X^7 - 42906868597132708796726553*X^6 + 9182069879786399682499482343*X^5
    - 1964962954274289532054889221401*X^4 + 420502072214697959859746293379815*X^3
    - 89987443453945363409985706783280409*X^2 + 19257312899144307769736941251622007527*X
    - 4121064960416881862723705427847109610777
  let A : ℤ[X] := 463917886127939357508086776201620966179
  let G : ℤ[X] := X^17 + X^16 + X^15 + X^13 + X^12 + X^10 + X^9 + X^8 + X^6 + X^5 + X^3 + X^2 + 2*X
  let Qp : ℤ[X] := -535*X^17 - 105*X^16 - 877*X^15 - 1056*X^14 - 770*X^13 - 1142*X^12 - 1376*X^11
    - 726*X^10 - 1053*X^9 - 1412*X^8 - 626*X^7 - 1542*X^6 - 1321*X^5 - 1090*X^4 - 1098*X^3 - 1287*X^2
    - 762*X - 953
  let Rp : ℤ[X] := 535*X^16 + 105*X^15 + 877*X^14 + 521*X^13 + 1200*X^12 + 370*X^11 + 662*X^10
    + 1442*X^9 - 91*X^8 + 999*X^7 + 1027*X^6 + 1273*X^5 - 44*X^4 + 1812*X^3 + 571*X^2 + 5*X + 1901
  let QP : ℤ[X] := -60*X^17 - 12*X^16 - 99*X^15 - 119*X^14 - 87*X^13 - 129*X^12 - 155*X^11 - 82*X^10
    - 119*X^9 - 159*X^8 - 71*X^7 - 174*X^6 - 149*X^5 - 123*X^4 - 124*X^3 - 145*X^2 - 86*X - 107
  let RP : ℤ[X] := 60*X^16 + 12*X^15 + 99*X^14 + 59*X^13 + 135*X^12 + 42*X^11 + 75*X^10 + 162*X^9
    - 10*X^8 + 113*X^7 + 116*X^6 + 143*X^5 - 4*X^4 + 204*X^3 + 64*X^2 + X + 214
  let C1 : ℤ[X] := X^16 - 213*X^15 + 45583*X^14 - 9754762*X^13 + 2087519069*X^12 - 446729080765*X^11
    + 95600023283710*X^10 - 20458404982713939*X^9 + 4378098666300782947*X^8 - 936913114588367550657*X^7
    + 200499406521910655840598*X^6 - 42906872995688880349887971*X^5 + 9182070821077420394876025795*X^4
    - 1964963155710567964503469520130*X^3 + 420502115322061544403742477307821*X^2
    - 89987452678921170502400890143873693*X + 19257314873289130487513790490788970304
  let C2 : ℤ[X] := -2167840811616977340519700770662198656
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2053 [Fact (Nat.Prime 2053)]
    (hpn : 2053 ≠ 19)
    (hmod : 2053 % 19 = 1) :
    NineteenCertificate 2053 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 51
  let Q : ℤ[X] := X^17 - 50*X^16 + 2551*X^15 - 130100*X^14 + 6635101*X^13 - 338390150*X^12
    + 17257897651*X^11 - 880152780200*X^10 + 44887791790201*X^9 - 2289277381300250*X^8
    + 116753146446312751*X^7 - 5954410468761950300*X^6 + 303674933906859465301*X^5
    - 15487421629249832730350*X^4 + 789858503091741469247851*X^3 - 40282783657678814931640400*X^2
    + 2054421966541619561513660401*X - 104775520293622597637196680450
  let A : ℤ[X] := 2602801527021311485385791867
  let G : ℤ[X] := X^16 + X^12 + X^8 + X^5 + X^4 - X^2 + X + 1
  let Qp : ℤ[X] := -907*X^17 + 184*X^16 - 26*X^15 + 419*X^14 + 307*X^13 - 140*X^12 + 74*X^11 - 575*X^10
    - 324*X^9 - 807*X^8 - 810*X^7 - 657*X^6 - 248*X^5 - 577*X^4 - 222*X^3 + 150*X^2 - 345*X + 264
  let Rp : ℤ[X] := 907*X^15 - 1091*X^14 + 210*X^13 - 445*X^12 + 1019*X^11 - 644*X^10 - 4*X^9 + 204*X^8
    + 768*X^7 - 161*X^6 - X^5 + 958*X^4 - 732*X^3 + 378*X^2 - 1708*X + 1789
  let QP : ℤ[X] := -22*X^17 + 5*X^16 + 11*X^14 + 8*X^13 - 3*X^12 + 2*X^11 - 14*X^10 - 8*X^9 - 20*X^8
    - 20*X^7 - 16*X^6 - 6*X^5 - 14*X^4 - 5*X^3 + 4*X^2 - 8*X + 7
  let RP : ℤ[X] := 22*X^15 - 27*X^14 + 5*X^13 - 11*X^12 + 25*X^11 - 16*X^10 + 5*X^8 + 19*X^7 - 4*X^6
    + 23*X^4 - 18*X^3 + 9*X^2 - 42*X + 44
  let C1 : ℤ[X] := X^15 - 51*X^14 + 2601*X^13 - 132651*X^12 + 6765202*X^11 - 345025302*X^10
    + 17596290402*X^9 - 897410810502*X^8 + 45767951335603*X^7 - 2334165518115753*X^6
    + 119042441423903403*X^5 - 6071164512619073552*X^4 + 309629390143572751153*X^3
    - 15791098897322210308803*X^2 + 805346043763432725748952*X - 41072648231935069013196551
  let C2 : ℤ[X] := 1020314203521036785033134
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2129 [Fact (Nat.Prime 2129)]
    (hpn : 2129 ≠ 19)
    (hmod : 2129 % 19 = 1) :
    NineteenCertificate 2129 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 429
  let Q : ℤ[X] := X^17 - 428*X^16 + 183613*X^15 - 78769976*X^14 + 33792319705*X^13 - 14496905153444*X^12
    + 6219172310827477*X^11 - 2668024921344987632*X^10 + 1144582691256999694129*X^9
    - 491025974549252868781340*X^8 + 210650143081629480707194861*X^7 - 90368911382019047223386595368*X^6
    + 38768262982886171258832849412873*X^5 - 16631584819658167470039292398122516*X^4
    + 7134949887633353844646856438794559365*X^3 - 3060893501794708799353501412242865967584*X^2
    + 1313123312269930074922652105852189500093537*X - 563329900963800002141817753410589295540127372
  let A : ℤ[X] := 113512694933522875020591740823458340904985741
  let G : ℤ[X] := X^17 + X^16 + X^15 + X^14 + X^13 + X^11 + X^9 + X^8 + X^7 + X^6 + X^5 + X^3 + X^2 + X + 2
  let Qp : ℤ[X] := -571*X^17 - 447*X^16 - 418*X^15 - 85*X^14 - 299*X^13 - 40*X^12 - 443*X^11 - 5*X^10
    - 555*X^9 - 924*X^8 - 169*X^7 - 456*X^6 - 815*X^5 - 92*X^4 + 575*X^3 - 282*X^2 - 946*X + 753
  let Rp : ℤ[X] := 571*X^16 + 447*X^15 + 418*X^14 + 85*X^13 + 299*X^12 - 531*X^11 + 567*X^10 - 537*X^9
    + 1012*X^8 + 739*X^7 + 761*X^6 - 161*X^5 + 1512*X^4 - 1432*X^3 - 382*X^2 + 516*X + 623
  let QP : ℤ[X] := -115*X^17 - 90*X^16 - 84*X^15 - 17*X^14 - 60*X^13 - 8*X^12 - 89*X^11 - X^10 - 112*X^9
    - 186*X^8 - 34*X^7 - 92*X^6 - 164*X^5 - 18*X^4 + 116*X^3 - 57*X^2 - 190*X + 152
  let RP : ℤ[X] := 115*X^16 + 90*X^15 + 84*X^14 + 17*X^13 + 60*X^12 - 107*X^11 + 114*X^10 - 108*X^9
    + 204*X^8 + 149*X^7 + 153*X^6 - 32*X^5 + 304*X^4 - 289*X^3 - 77*X^2 + 104*X + 125
  let C1 : ℤ[X] := X^16 - 428*X^15 + 183613*X^14 - 78769976*X^13 + 33792319705*X^12
    - 14496905153445*X^11 + 6219172310827906*X^10 - 2668024921345171674*X^9 + 1144582691257078648147*X^8
    - 491025974549286740055062*X^7 + 210650143081644011483621599*X^6 - 90368911382025280926473665970*X^5
    + 38768262982888845517457202701131*X^4 - 16631584819659314726989139958785199*X^3
    + 7134949887633846017878341042318850372*X^2 - 3060893501794919941669808307154786809587*X
    + 1313123312270020654976347763769403541312824
  let C2 : ℤ[X] := -264598356488416562228676933140946040029686
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2243 [Fact (Nat.Prime 2243)]
    (hpn : 2243 ≠ 19)
    (hmod : 2243 % 19 = 1) :
    NineteenCertificate 2243 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 72
  let Q : ℤ[X] := X^17 - 71*X^16 + 5113*X^15 - 368135*X^14 + 26505721*X^13 - 1908411911*X^12
    + 137405657593*X^11 - 9893207346695*X^10 + 712310928962041*X^9 - 51286386885266951*X^8
    + 3692619855739220473*X^7 - 265868629613223874055*X^6 + 19142541332152118931961*X^5
    - 1378262975914952563101191*X^4 + 99234934265876584543285753*X^3 - 7144915267143114087116574215*X^2
    + 514433899234304214272393343481*X - 37039240744869903427612320730631
  let A : ℤ[X] := 1188954673932515847876989341331
  let G : ℤ[X] := -X^17 - X^12 - X^7 + X^5
  let Qp : ℤ[X] := -97*X^17 + 158*X^16 - 258*X^15 + 535*X^14 - 486*X^13 - 993*X^12 - 377*X^11 + 131*X^10
    - 557*X^9 - 367*X^8 - 589*X^7 - 306*X^6 - 495*X^5 - 345*X^4 + 70*X^3 - 651*X^2 - 328*X - 1154
  let Rp : ℤ[X] := -97*X^16 + 255*X^15 - 416*X^14 + 793*X^13 - 1021*X^12 - 604*X^11 + 871*X^10 + 92*X^9
    + 105*X^8 - 831*X^7 - 826*X^6 + 1154*X^5 - 2243*X + 2243
  let QP : ℤ[X] := -3*X^17 + 5*X^16 - 8*X^15 + 17*X^14 - 16*X^13 - 32*X^12 - 12*X^11 + 4*X^10 - 18*X^9
    - 12*X^8 - 19*X^7 - 10*X^6 - 16*X^5 - 11*X^4 + 2*X^3 - 21*X^2 - 11*X - 37
  let RP : ℤ[X] := -3*X^16 + 8*X^15 - 13*X^14 + 25*X^13 - 33*X^12 - 19*X^11 + 28*X^10 + 3*X^9 + 3*X^8
    - 27*X^7 - 26*X^6 + 37*X^5 - X^2 - 71*X + 72
  let C1 : ℤ[X] := -X^16 + 72*X^15 - 5184*X^14 + 373248*X^13 - 26873856*X^12 + 1934917631*X^11
    - 139314069432*X^10 + 10030612999104*X^9 - 722204135935488*X^8 + 51998697787355136*X^7
    - 3743906240689569793*X^6 + 269561249329649025096*X^5 - 19408409951734729806911*X^4
    + 1397405516524900546097592*X^3 - 100613197189792839319026624*X^2 + 7244150197665084430969916928*X
    - 521578814231886079029834018816
  let C2 : ℤ[X] := 16742610175967809937649598464
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2281 [Fact (Nat.Prime 2281)]
    (hpn : 2281 ≠ 19)
    (hmod : 2281 % 19 = 1) :
    NineteenCertificate 2281 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 32
  let Q : ℤ[X] := X^17 - 31*X^16 + 993*X^15 - 31775*X^14 + 1016801*X^13 - 32537631*X^12
    + 1041204193*X^11 - 33318534175*X^10 + 1066193093601*X^9 - 34118178995231*X^8 + 1091781727847393*X^7
    - 34937015291116575*X^6 + 1117984489315730401*X^5 - 35775503658103372831*X^4
    + 1144816117059307930593*X^3 - 36634115745897853778975*X^2 + 1172291703868731320927201*X
    - 37513334523799402269670431
  let A : ℤ[X] := 526272119579825020880953
  let G : ℤ[X] := -X^17 - X^16 - X^15 - X^13 - X^12 - X^11 - X^9 - X^8 - X^7 - X^6 - X^5 - 2*X^4 - X^2 - X - 1
  let Qp : ℤ[X] := 344*X^17 + 741*X^16 - 558*X^15 - 48*X^14 - 401*X^13 - 510*X^12 + 697*X^11 + 850*X^10
    + 516*X^9 - 201*X^8 - 67*X^7 + 207*X^6 + 563*X^5 + 576*X^4 + 160*X^3 - 214*X^2 + 349*X + 581
  let Rp : ℤ[X] := 344*X^16 + 741*X^15 - 558*X^14 - 392*X^13 - 798*X^12 + 789*X^11 + 187*X^10 + 859*X^9
    + 228*X^8 - 109*X^7 - 730*X^6 + 894*X^5 + 1389*X^4 - 421*X^3 - 214*X^2 - 1932*X + 2862
  let QP : ℤ[X] := 5*X^17 + 10*X^16 - 8*X^15 - X^14 - 6*X^13 - 7*X^12 + 10*X^11 + 12*X^10 + 7*X^9
    - 3*X^8 - X^7 + 3*X^6 + 8*X^5 + 8*X^4 + 2*X^3 - 3*X^2 + 5*X + 8
  let RP : ℤ[X] := 5*X^16 + 10*X^15 - 8*X^14 - 6*X^13 - 11*X^12 + 11*X^11 + 3*X^10 + 12*X^9 + 3*X^8
    - 2*X^7 - 10*X^6 + 13*X^5 + 19*X^4 - 6*X^3 - 4*X^2 - 26*X + 40
  let C1 : ℤ[X] := -X^16 + 31*X^15 - 993*X^14 + 31776*X^13 - 1016833*X^12 + 32538655*X^11
    - 1041236961*X^10 + 33319582752*X^9 - 1066226648065*X^8 + 34119252738079*X^7 - 1091816087618529*X^6
    + 34938114803792927*X^5 - 1118019673721373665*X^4 + 35776629559083957278*X^3
    - 1144852145890686632896*X^2 + 36635268668501972252671*X - 1172328597392063112085473
  let C2 : ℤ[X] := 16446521313698386491335
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2357 [Fact (Nat.Prime 2357)]
    (hpn : 2357 ≠ 19)
    (hmod : 2357 % 19 = 1) :
    NineteenCertificate 2357 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 314
  let Q : ℤ[X] := X^17 - 313*X^16 + 98283*X^15 - 30860861*X^14 + 9690310355*X^13 - 3042757451469*X^12
    + 955425839761267*X^11 - 300003713685037837*X^10 + 94201166097101880819*X^9
    - 29579166154489990577165*X^8 + 9287858172509857041229811*X^7 - 2916387466168095110946160653*X^6
    + 915745664376781864837094445043*X^5 - 287544138614309505558847655743501*X^4
    + 90288859524893184745478163903459315*X^3 - 28350701890816460010080143465686224909*X^2
    + 8902120393716368443165165048225474621427*X - 2795265803626939691153861825142799031128077
  let A : ℤ[X] := 372385855892600366152869161262129357562247
  let G : ℤ[X] := -2*X^17 - 4*X^16 - X^15 - 3*X^13 - 4*X^12 - X^11 - X^10 - 4*X^9 - 4*X^8 - X^6 - 4*X^5
    - 3*X^4 - 2*X^2 - 4*X - 2
  let Qp : ℤ[X] := -1331*X^17 - 586*X^16 - 1173*X^15 - 701*X^14 - 418*X^13 + 286*X^12 - 1569*X^11
    - 1278*X^10 - 729*X^9 - 1054*X^8 - 355*X^7 - 640*X^6 - 716*X^5 - 422*X^4 - 815*X^3 + 23*X^2 - 1482*X
    - 312
  let Rp : ℤ[X] := -2662*X^16 - 3834*X^15 + 475*X^14 - 659*X^13 - 2126*X^12 - 77*X^11 - 723*X^10
    - 7652*X^9 - 2022*X^8 + 2622*X^7 - 715*X^6 - 5450*X^5 - 492*X^4 + 2004*X^3 - 2294*X^2 - 5945*X
    + 1733
  let QP : ℤ[X] := -177*X^17 - 78*X^16 - 156*X^15 - 93*X^14 - 55*X^13 + 38*X^12 - 209*X^11 - 170*X^10
    - 97*X^9 - 140*X^8 - 47*X^7 - 85*X^6 - 95*X^5 - 56*X^4 - 108*X^3 + 3*X^2 - 197*X - 41
  let RP : ℤ[X] := -354*X^16 - 510*X^15 + 63*X^14 - 87*X^13 - 281*X^12 - 10*X^11 - 99*X^10 - 1018*X^9
    - 266*X^8 + 349*X^7 - 97*X^6 - 724*X^5 - 63*X^4 + 266*X^3 - 307*X^2 - 789*X + 232
  let C1 : ℤ[X] := -2*X^16 + 624*X^15 - 195937*X^14 + 61524218*X^13 - 19318604455*X^12
    + 6066041798866*X^11 - 1904737124843925*X^10 + 598087457200992449*X^9 - 187799461561111628990*X^8
    + 58969030930189051502856*X^7 - 18516275712079362171896784*X^6 + 5814110573592919721975590175*X^5
    - 1825630720108176792700335314954*X^4 + 573248046113967512907905288895553*X^3
    - 179999886479785799053082260713203642*X^2 + 56519964354652740902667829863945943586*X
    - 17747268807360960643437698577279026286008
  let C2 : ℤ[X] := 2364294614132940874857631460867888949430
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2699 [Fact (Nat.Prime 2699)]
    (hpn : 2699 ≠ 19)
    (hmod : 2699 % 19 = 1) :
    NineteenCertificate 2699 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 33
  let Q : ℤ[X] := X^17 - 32*X^16 + 1057*X^15 - 34880*X^14 + 1151041*X^13 - 37984352*X^12
    + 1253483617*X^11 - 41364959360*X^10 + 1365043658881*X^9 - 45046440743072*X^8 + 1486532544521377*X^7
    - 49055573969205440*X^6 + 1618833940983779521*X^5 - 53421520052464724192*X^4
    + 1762910161731335898337*X^3 - 58176035337134084645120*X^2 + 1919809166125424793288961*X
    - 63353702482139018178535712
  let A : ℤ[X] := 774609922901292182249603
  let G : ℤ[X] := X^8 + X^3 - X + 1
  let Qp : ℤ[X] := 810*X^17 + 1070*X^16 + 587*X^15 + 332*X^14 + 650*X^13 + 952*X^12 + 1782*X^11
    + 1382*X^10 + 1087*X^9 + 26*X^8 - 48*X^7 - 305*X^6 + 79*X^5 + 902*X^4 + 733*X^3 + 912*X^2 + 403*X
    + 1006
  let Rp : ℤ[X] := -810*X^7 - 260*X^6 + 483*X^5 + 255*X^4 - 318*X^3 - 1112*X^2 - 1090*X + 1693
  let QP : ℤ[X] := 10*X^17 + 13*X^16 + 7*X^15 + 4*X^14 + 8*X^13 + 12*X^12 + 22*X^11 + 17*X^10 + 13*X^9
    - X^7 - 4*X^6 + X^5 + 11*X^4 + 9*X^3 + 11*X^2 + 5*X + 12
  let RP : ℤ[X] := -10*X^7 - 3*X^6 + 6*X^5 + 3*X^4 - 4*X^3 - 14*X^2 - 13*X + 21
  let C1 : ℤ[X] := X^7 - 33*X^6 + 1089*X^5 - 35937*X^4 + 1185921*X^3 - 39135392*X^2 + 1291467936*X
    - 42618441889
  let C2 : ℤ[X] := 521085062
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2851 [Fact (Nat.Prime 2851)]
    (hpn : 2851 ≠ 19)
    (hmod : 2851 % 19 = 1) :
    NineteenCertificate 2851 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 3
  let Q : ℤ[X] := X^17 - 2*X^16 + 7*X^15 - 20*X^14 + 61*X^13 - 182*X^12 + 547*X^11 - 1640*X^10
    + 4921*X^9 - 14762*X^8 + 44287*X^7 - 132860*X^6 + 398581*X^5 - 1195742*X^4 + 3587227*X^3
    - 10761680*X^2 + 32285041*X - 96855122
  let A : ℤ[X] := 101917
  let G : ℤ[X] := X^14 + X^11 + X^7 + X^6 + 1
  let Qp : ℤ[X] := 116*X^17 - 232*X^16 + 812*X^15 + 531*X^14 + 1374*X^13 + 1696*X^12 + 730*X^11
    + 777*X^10 + 636*X^9 + 1059*X^8 - 210*X^7 + 746*X^6 + 729*X^5 + 780*X^4 + 627*X^3 + 1086*X^2 - 291*X
    + 989
  let Rp : ℤ[X] := -116*X^13 + 348*X^12 - 1044*X^11 + 165*X^10 - 495*X^9 - 1366*X^8 + 1247*X^7
    - 1006*X^6 + 51*X^5 - 153*X^4 + 459*X^3 - 1377*X^2 - 1571*X + 1862
  let QP : ℤ[X] := X^15 + X^14 + 2*X^13 + 2*X^12 + X^11 + X^10 + X^9 + X^8 + X^6 + X^5 + X^4 + X^3 + X^2 + 1
  let RP : ℤ[X] := -X^11 - X^9 - X^8 + X^7 - X^6 - 2*X^2 - X + 2
  let C1 : ℤ[X] := X^13 - 3*X^12 + 9*X^11 - 26*X^10 + 78*X^9 - 234*X^8 + 702*X^7 - 2105*X^6 + 6316*X^5
    - 18948*X^4 + 56844*X^3 - 170532*X^2 + 511596*X - 1534788
  let C2 : ℤ[X] := 1615
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_2927 [Fact (Nat.Prime 2927)]
    (hpn : 2927 ≠ 19)
    (hmod : 2927 % 19 = 1) :
    NineteenCertificate 2927 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 17
  let Q : ℤ[X] := X^17 - 16*X^16 + 273*X^15 - 4640*X^14 + 78881*X^13 - 1340976*X^12 + 22796593*X^11
    - 387542080*X^10 + 6588215361*X^9 - 111999661136*X^8 + 1903994239313*X^7 - 32367902068320*X^6
    + 550254335161441*X^5 - 9354323697744496*X^4 + 159023502861656433*X^3 - 2703399548648159360*X^2
    + 45957792327018709121*X - 781282469559318055056
  let A : ℤ[X] := 4537684312438813439
  let G : ℤ[X] := X^17 + X^14 + X^13 + X^12 + X^11 + X^10 + X^9 + X^8 + 2*X^7 + X^6 + X^5 + X^4 + X^3
    + X^2 + X + 1
  let Qp : ℤ[X] := 513*X^17 + 573*X^16 - 447*X^15 - 669*X^14 + 178*X^13 + 414*X^12 - 671*X^11 + 212*X^10
    - 164*X^9 + 374*X^8 + 9*X^7 + 360*X^6 + 247*X^5 - 759*X^4 - 1219*X^3 + 747*X^2 - 478*X - 142
  let Rp : ℤ[X] := -513*X^16 - 60*X^15 + 1020*X^14 - 291*X^13 - 1420*X^12 + 211*X^11 + 1754*X^10
    - 1061*X^9 - 38*X^8 + 133*X^7 - 360*X^6 - 247*X^5 + 759*X^4 + 1219*X^3 - 747*X^2 - 2449*X + 3069
  let QP : ℤ[X] := 3*X^17 + 3*X^16 - 3*X^15 - 4*X^14 + X^13 + 2*X^12 - 4*X^11 + X^10 - X^9 + 2*X^8
    + 2*X^6 + X^5 - 5*X^4 - 7*X^3 + 4*X^2 - 3*X - 1
  let RP : ℤ[X] := -3*X^16 + 6*X^14 - 2*X^13 - 8*X^12 + 2*X^11 + 10*X^10 - 6*X^9 + X^7 - 2*X^6 - X^5
    + 5*X^4 + 7*X^3 - 5*X^2 - 13*X + 18
  let C1 : ℤ[X] := X^16 - 17*X^15 + 289*X^14 - 4912*X^13 + 83505*X^12 - 1419584*X^11 + 24132929*X^10
    - 410259792*X^9 + 6974416465*X^8 - 118565079904*X^7 + 2015606358370*X^6 - 34265308092289*X^5
    + 582510237568914*X^4 - 9902674038671537*X^3 + 168345458657416130*X^2 - 2861872797176074209*X
    + 48651837551993261554
  let C2 : ℤ[X] := -282569606554111871
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_3041 [Fact (Nat.Prime 3041)]
    (hpn : 3041 ≠ 19)
    (hmod : 3041 % 19 = 1) :
    NineteenCertificate 3041 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 245
  let Q : ℤ[X] := X^17 - 244*X^16 + 59781*X^15 - 14646344*X^14 + 3588354281*X^13 - 879146798844*X^12
    + 215390965716781*X^11 - 52770786600611344*X^10 + 12928842717149779281*X^9
    - 3167566465701695923844*X^8 + 776053784096915501341781*X^7 - 190133177103744297828736344*X^6
    + 46582628390417352968040404281*X^5 - 11412743955652251477169899048844*X^4
    + 2796122269134801611906625266966781*X^3 - 685049955938026394917123190406861344*X^2
    + 167837239204816466754695181649681029281*X - 41120123605180034354900319504171852173844
  let A : ℤ[X] := 3312867570953340485679243103756035443141
  let G : ℤ[X] := -X^17 - X^16 - X^14 - X^10 - X^7 - X^5 - 1
  let Qp : ℤ[X] := 374*X^17 - 26*X^16 + 662*X^15 - 643*X^14 - 223*X^13 + 271*X^12 + 881*X^11 + 440*X^10
    - 991*X^9 - 111*X^8 + 200*X^7 + 30*X^6 - 894*X^5 + 452*X^4 - 890*X^3 - 528*X^2 - 1029*X + 76
  let Rp : ℤ[X] := 374*X^16 - 26*X^15 + 288*X^14 - 243*X^13 - 1285*X^12 + 1602*X^11 - 201*X^10 + 963*X^9
    - 1778*X^8 + 747*X^7 - 181*X^6 - 1270*X^5 + 1342*X^4 - 362*X^3 + 501*X^2 - 4146*X + 3117
  let QP : ℤ[X] := 30*X^17 - 2*X^16 + 53*X^15 - 52*X^14 - 18*X^13 + 22*X^12 + 71*X^11 + 35*X^10 - 80*X^9
    - 9*X^8 + 16*X^7 + 2*X^6 - 72*X^5 + 36*X^4 - 72*X^3 - 43*X^2 - 83*X + 6
  let RP : ℤ[X] := 30*X^16 - 2*X^15 + 23*X^14 - 20*X^13 - 103*X^12 + 129*X^11 - 16*X^10 + 77*X^9
    - 143*X^8 + 60*X^7 - 15*X^6 - 102*X^5 + 108*X^4 - 29*X^3 + 39*X^2 - 333*X + 251
  let C1 : ℤ[X] := -X^16 + 244*X^15 - 59780*X^14 + 14646099*X^13 - 3588294255*X^12 + 879132092475*X^11
    - 215387362656375*X^10 + 52769903850811874*X^9 - 12928626443448909130*X^8
    + 3167513478644982736850*X^7 - 776040802268020770528251*X^6 + 190129996555665088779421495*X^5
    - 46581849156137946750958266276*X^4 + 11412553043253796953984775237620*X^3
    - 2796075495597180253726269933216900*X^2 + 685038496421309162162936133638140500*X
    - 167834431623220744729919352741344422500
  let C2 : ℤ[X] := 13521682258365367464265123782186577939
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_3079 [Fact (Nat.Prime 3079)]
    (hpn : 3079 ≠ 19)
    (hmod : 3079 % 19 = 1) :
    NineteenCertificate 3079 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 27
  let Q : ℤ[X] := X^17 - 26*X^16 + 703*X^15 - 18980*X^14 + 512461*X^13 - 13836446*X^12 + 373584043*X^11
    - 10086769160*X^10 + 272342767321*X^9 - 7353254717666*X^8 + 198537877376983*X^7
    - 5360522689178540*X^6 + 144734112607820581*X^5 - 3907821040411155686*X^4
    + 105511168091101203523*X^3 - 2848801538459732495120*X^2 + 76917641538412777368241*X
    - 2076776321537144988942506
  let A : ℤ[X] := 18211419513316958331097
  let G : ℤ[X] := X^7 + X^3 + X + 1
  let Qp : ℤ[X] := -940*X^17 - 192*X^16 - 1914*X^15 - 1605*X^14 - 711*X^13 - 217*X^12 - 1239*X^11
    - 1356*X^10 - 1276*X^9 - 357*X^8 - 538*X^7 - 1809*X^6 - 1361*X^5 - 1141*X^4 - 923*X^3 - 651*X^2
    - 1837*X - 605
  let Rp : ℤ[X] := 940*X^6 - 748*X^5 + 1722*X^4 - 309*X^3 + 46*X^2 - 1242*X + 3684
  let QP : ℤ[X] := -8*X^17 - 2*X^16 - 17*X^15 - 14*X^14 - 6*X^13 - 2*X^12 - 11*X^11 - 12*X^10 - 11*X^9
    - 3*X^8 - 5*X^7 - 16*X^6 - 12*X^5 - 10*X^4 - 8*X^3 - 6*X^2 - 16*X - 5
  let RP : ℤ[X] := 8*X^6 - 6*X^5 + 15*X^4 - 3*X^3 - 10*X + 32
  let C1 : ℤ[X] := X^6 - 27*X^5 + 729*X^4 - 19683*X^3 + 531442*X^2 - 14348934*X + 387421219
  let C2 : ℤ[X] := -3397328
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_3307 [Fact (Nat.Prime 3307)]
    (hpn : 3307 ≠ 19)
    (hmod : 3307 % 19 = 1) :
    NineteenCertificate 3307 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 12
  let Q : ℤ[X] := X^17 - 11*X^16 + 133*X^15 - 1595*X^14 + 19141*X^13 - 229691*X^12 + 2756293*X^11
    - 33075515*X^10 + 396906181*X^9 - 4762874171*X^8 + 57154490053*X^7 - 685853880635*X^6
    + 8230246567621*X^5 - 98762958811451*X^4 + 1185155505737413*X^3 - 14221866068848955*X^2
    + 170662392826187461*X - 2047948713914249531
  let A : ℤ[X] := 7431322820372239
  let G : ℤ[X] := 2*X^17 - 2*X^15 + 2*X^13 - 2*X^11 + X^10 + 2*X^9 - X^8 - 2*X^7 + 2*X^6 + X^5 - X^4
    - X^3 + 2*X^2 + X - 2
  let Qp : ℤ[X] := 485*X^17 + 1279*X^16 + 1672*X^15 + 263*X^14 + 636*X^13 - 533*X^12 + 267*X^11
    + 588*X^10 + 43*X^9 - 31*X^8 + 857*X^7 + 122*X^6 - 979*X^5 - 995*X^4 - 803*X^3 + 200*X^2 + 1392*X
    + 316
  let Rp : ℤ[X] := -970*X^16 - 1588*X^15 + 184*X^14 + 4406*X^13 - 930*X^12 - 2068*X^11 - 670*X^10
    + 941*X^9 + 966*X^8 - 1186*X^7 - 1333*X^6 + 1798*X^5 + 4395*X^4 - 2650*X^3 - 4092*X^2 - 1471*X
    + 3939
  let QP : ℤ[X] := 2*X^17 + 5*X^16 + 6*X^15 + X^14 + 2*X^13 - 2*X^12 + X^11 + 2*X^10 + 3*X^7 - 4*X^5
    - 4*X^4 - 3*X^3 + X^2 + 5*X + 1
  let RP : ℤ[X] := -4*X^16 - 6*X^15 + 2*X^14 + 16*X^13 - 4*X^12 - 8*X^11 - 2*X^10 + 4*X^9 + 3*X^8
    - 5*X^7 - 4*X^6 + 8*X^5 + 15*X^4 - 11*X^3 - 15*X^2 - 4*X + 14
  let C1 : ℤ[X] := 2*X^16 - 24*X^15 + 286*X^14 - 3432*X^13 + 41186*X^12 - 494232*X^11 + 5930782*X^10
    - 71169383*X^9 + 854032598*X^8 - 10248391177*X^7 + 122980694122*X^6 - 1475768329462*X^5
    + 17709219953545*X^4 - 212510639442541*X^3 + 2550127673310491*X^2 - 30601532079725890*X
    + 367218384956710681
  let C2 : ℤ[X] := -1332513038851082
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_3877 [Fact (Nat.Prime 3877)]
    (hpn : 3877 ≠ 19)
    (hmod : 3877 % 19 = 1) :
    NineteenCertificate 3877 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 313
  let Q : ℤ[X] := X^17 - 312*X^16 + 97657*X^15 - 30566640*X^14 + 9567358321*X^13 - 2994583154472*X^12
    + 937304527349737*X^11 - 293376317060467680*X^10 + 91826787239926383841*X^9
    - 28741784406096958142232*X^8 + 8996178519108347898518617*X^7 - 2815803876480912892236327120*X^6
    + 881346613338525735269970388561*X^5 - 275861489974958555139500731619592*X^4
    + 86344646362162027758663728996932297*X^3 - 27025874311356714688461747176039808960*X^2
    + 8459098659454651697488526866100460204481*X - 2647697880409305981313908909089444044002552
  let A : ℤ[X] := 213755335715272832641540750205054419853701
  let G : ℤ[X] := -2*X^17 - 2*X^16 - X^14 - 3*X^13 - 2*X^12 - 3*X^9 - 2*X^8 - 2*X^6 - 3*X^5 - X^4
    - 2*X^2 - 3*X - 1
  let Qp : ℤ[X] := -1475*X^17 - 1163*X^16 - 1894*X^15 - 1834*X^14 - 1229*X^13 - 621*X^12 - 952*X^11
    - 2028*X^10 + 1338*X^9 - 1553*X^8 - 11*X^7 - 1909*X^6 - 1016*X^5 - 1381*X^4 + 431*X^3 - 683*X^2
    - 931*X - 847
  let Rp : ℤ[X] := -2950*X^16 - 2326*X^15 - 838*X^14 - 2817*X^13 - 2783*X^12 - 319*X^11 - 955*X^10
    - 3491*X^9 + 2698*X^8 + 1639*X^7 - 5120*X^6 - 5468*X^5 + 1179*X^4 + 1690*X^3 - 1698*X^2 - 6502*X
    + 3030
  let QP : ℤ[X] := -119*X^17 - 94*X^16 - 153*X^15 - 148*X^14 - 99*X^13 - 50*X^12 - 77*X^11 - 163*X^10
    + 108*X^9 - 125*X^8 - X^7 - 154*X^6 - 82*X^5 - 111*X^4 + 35*X^3 - 55*X^2 - 75*X - 68
  let RP : ℤ[X] := -238*X^16 - 188*X^15 - 68*X^14 - 227*X^13 - 224*X^12 - 26*X^11 - 78*X^10 - 280*X^9
    + 219*X^8 + 131*X^7 - 414*X^6 - 440*X^5 + 96*X^4 + 136*X^3 - 138*X^2 - 523*X + 245
  let C1 : ℤ[X] := -2*X^16 + 624*X^15 - 195312*X^14 + 61132655*X^13 - 19134521018*X^12
    + 5989105078632*X^11 - 1874589889611816*X^10 + 586746635448498408*X^9 - 183651696895380001707*X^8
    + 57482981128253940534289*X^7 - 17992173093143483387232457*X^6 + 5631550178153910300203759039*X^5
    - 1762675205762173923963776579210*X^4 + 551717339403560438200662069292729*X^3
    - 172687527233314417156807227688624177*X^2 + 54051196024027412570080662266539367399*X
    - 16918024355520580134435247289426821995890
  let C2 : ℤ[X] := 1365834826741795610543779314312766387597
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4219 [Fact (Nat.Prime 4219)]
    (hpn : 4219 ≠ 19)
    (hmod : 4219 % 19 = 1) :
    NineteenCertificate 4219 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 447
  let Q : ℤ[X] := X^17 - 446*X^16 + 199363*X^15 - 89115260*X^14 + 39834521221*X^13 - 17806030985786*X^12
    + 7959295850646343*X^11 - 3557805245238915320*X^10 + 1590338944621795148041*X^9
    - 710881508245942431174326*X^8 + 317764034185936266734923723*X^7
    - 142040523281113511230510904180*X^6 + 63492113906657739520038374168461*X^5
    - 28380974916276009565457153253302066*X^4 + 12686295787575376275759347504226023503*X^3
    - 5670774217046193195264428334389032505840*X^2 + 2534836075019648358283199465471897530110481*X
    - 1133071725533782816152590161065938195959385006
  let A : ℤ[X] := 120048130199952813183268026071693380799678857
  let G : ℤ[X] := -X^17 - X^16 - X^14 - X^12 - X^11 - X^7 - X^6 - X
  let Qp : ℤ[X] := 211*X^17 + 2931*X^16 + 2163*X^15 - 499*X^14 - 343*X^13 + 1648*X^12 + 1880*X^11
    - 568*X^10 + 967*X^9 + 2519*X^8 + 691*X^7 - 679*X^6 - 44*X^5 + 3003*X^4 - 488*X^3 - 1041*X^2
    + 1448*X + 2681
  let Rp : ℤ[X] := 211*X^16 + 2931*X^15 + 1952*X^14 - 3219*X^13 + 214*X^12 + 1590*X^11 + 2492*X^10
    - 108*X^9 - 2352*X^8 + 813*X^7 - 366*X^6 + 3491*X^5 + 553*X^4 - 2489*X^3 - 1233*X^2 - 1538*X + 4219
  let QP : ℤ[X] := 23*X^17 + 311*X^16 + 229*X^15 - 53*X^14 - 36*X^13 + 175*X^12 + 199*X^11 - 60*X^10
    + 103*X^9 + 267*X^8 + 73*X^7 - 72*X^6 - 4*X^5 + 318*X^4 - 52*X^3 - 110*X^2 + 154*X + 284
  let RP : ℤ[X] := 23*X^16 + 311*X^15 + 206*X^14 - 341*X^13 + 23*X^12 + 169*X^11 + 264*X^10 - 12*X^9
    - 249*X^8 + 86*X^7 - 38*X^6 + 370*X^5 + 58*X^4 - 264*X^3 - 131*X^2 - 162*X + 447
  let C1 : ℤ[X] := -X^16 + 446*X^15 - 199362*X^14 + 89114813*X^13 - 39834321411*X^12
    + 17805941670716*X^11 - 7959255926810053*X^10 + 3557787399284093691*X^9 - 1590330967479989879877*X^8
    + 710877942463555476305019*X^7 - 317762440281209297908343494*X^6
    + 142039810805700556165029541817*X^5 - 63491795430148148605768205192199*X^4
    + 28380832557276222426778387720912953*X^3 - 12686232153102471424769939311248089991*X^2
    + 5670745772436804726872162872127896225977*X - 2534823360279251712911856803841169613011720
  let C2 : ℤ[X] := 268562702546770683970514337832899458880360
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4409 [Fact (Nat.Prime 4409)]
    (hpn : 4409 ≠ 19)
    (hmod : 4409 % 19 = 1) :
    NineteenCertificate 4409 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 261
  let Q : ℤ[X] := X^17 - 260*X^16 + 67861*X^15 - 17711720*X^14 + 4622758921*X^13 - 1206540078380*X^12
    + 314906960457181*X^11 - 82190716679324240*X^10 + 21451777053303626641*X^9
    - 5598913810912246553300*X^8 + 1461316504648096350411301*X^7 - 381403607713153147457349560*X^6
    + 99546341613132971486368235161*X^5 - 25981595161027705557942109377020*X^4
    + 6781196337028231150622890547402221*X^3 - 1769892243964368330312574432871979680*X^2
    + 461941875674700134211581926979586696481*X - 120566829551096735029222882941672127781540
  let A : ℤ[X] := 7137206285515138998100969028754008925149
  let G : ℤ[X] := X^15 + X^14 + X^13 + X^12 + X^11 + X^10 + X^7 + X^6 + X^5 + X^4 + X^2 + X + 1
  let Qp : ℤ[X] := 982*X^17 + 402*X^16 + 1876*X^15 + 745*X^14 + 533*X^13 + 2957*X^12 + 780*X^11
    + 216*X^10 + 1923*X^9 + 1705*X^8 + 1286*X^7 + 420*X^6 + 1587*X^5 + 1221*X^4 - 251*X^3 + 358*X^2
    + 133*X + 1541
  let Rp : ℤ[X] := -982*X^14 - 402*X^13 - 1876*X^12 - 745*X^11 - 533*X^10 - 2957*X^9 + 202*X^8 + 186*X^7
    - 1029*X^6 - 1362*X^5 - 2629*X^4 + 1792*X^3 - 358*X^2 - 4542*X + 2868
  let QP : ℤ[X] := 58*X^17 + 24*X^16 + 111*X^15 + 44*X^14 + 32*X^13 + 175*X^12 + 46*X^11 + 13*X^10
    + 114*X^9 + 101*X^8 + 76*X^7 + 25*X^6 + 94*X^5 + 72*X^4 - 15*X^3 + 21*X^2 + 8*X + 91
  let RP : ℤ[X] := -58*X^14 - 24*X^13 - 111*X^12 - 44*X^11 - 32*X^10 - 175*X^9 + 12*X^8 + 11*X^7
    - 61*X^6 - 81*X^5 - 155*X^4 + 106*X^3 - 22*X^2 - 268*X + 170
  let C1 : ℤ[X] := X^14 - 260*X^13 + 67861*X^12 - 17711720*X^11 + 4622758921*X^10 - 1206540078380*X^9
    + 314906960457180*X^8 - 82190716679323980*X^7 + 21451777053303558781*X^6
    - 5598913810912228841840*X^5 + 1461316504648091727720241*X^4 - 381403607713151940934982900*X^3
    + 99546341613132656584030536900*X^2 - 25981595161027623368431970130899*X
    + 6781196337028209699160744204164640
  let C2 : ℤ[X] := -401427136304006062935122303762071
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4447 [Fact (Nat.Prime 4447)]
    (hpn : 4447 ≠ 19)
    (hmod : 4447 % 19 = 1) :
    NineteenCertificate 4447 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 96
  let Q : ℤ[X] := X^17 - 95*X^16 + 9121*X^15 - 875615*X^14 + 84059041*X^13 - 8069667935*X^12
    + 774688121761*X^11 - 74370059689055*X^10 + 7139525730149281*X^9 - 685394470094330975*X^8
    + 65797869129055773601*X^7 - 6316595436389354265695*X^6 + 606393161893378009506721*X^5
    - 58213743541764288912645215*X^4 + 5588519380009371735613940641*X^3
    - 536497860480899686618938301535*X^2 + 51503794606166369915418076947361*X
    - 4944364282191971511880135386946655
  let A : ℤ[X] := 106736894780847597288170226477823
  let G : ℤ[X] := X^17 + X^16 - X^15 + X^13 + X^12 - X^11 + X^9 - X^7 + X^6 + X^5 + X^2 + X - 1
  let Qp : ℤ[X] := -151*X^17 + 1004*X^16 + 1299*X^15 - 339*X^14 + 1264*X^13 - 1426*X^12 - 1112*X^11
    - 127*X^10 - 1300*X^9 + 133*X^8 + 422*X^7 - 640*X^6 - 969*X^5 - 514*X^4 + 276*X^3 + 35*X^2 + 936*X
    - 1067
  let Rp : ℤ[X] := 151*X^16 - 1004*X^15 - 1601*X^14 + 2498*X^13 + 481*X^12 - 1555*X^11 + 2378*X^10
    - 1491*X^9 + 983*X^8 - 981*X^7 + 638*X^6 + 1161*X^5 - 130*X^4 - 861*X^3 - 1837*X^2 - 1377*X + 3380
  let QP : ℤ[X] := -3*X^17 + 22*X^16 + 28*X^15 - 7*X^14 + 27*X^13 - 31*X^12 - 24*X^11 - 3*X^10 - 28*X^9
    + 3*X^8 + 9*X^7 - 14*X^6 - 21*X^5 - 11*X^4 + 6*X^3 + X^2 + 20*X - 23
  let RP : ℤ[X] := 3*X^16 - 22*X^15 - 34*X^14 + 54*X^13 + 10*X^12 - 33*X^11 + 51*X^10 - 32*X^9 + 21*X^8
    - 21*X^7 + 14*X^6 + 25*X^5 - 3*X^4 - 19*X^3 - 40*X^2 - 29*X + 73
  let C1 : ℤ[X] := X^16 - 95*X^15 + 9119*X^14 - 875424*X^13 + 84040705*X^12 - 8067907679*X^11
    + 774519137183*X^10 - 74353837169568*X^9 + 7137968368278529*X^8 - 685244963354738784*X^7
    + 65783516482054923263*X^6 - 6315217582277272633247*X^5 + 606260887898618172791713*X^4
    - 58201045238267344588004448*X^3 + 5587300342873665080448427008*X^2
    - 536380832915871847723048992767*X + 51492559959923697381412703305633
  let C2 : ℤ[X] := -1111600125062440959886579608127
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4523 [Fact (Nat.Prime 4523)]
    (hpn : 4523 ≠ 19)
    (hmod : 4523 % 19 = 1) :
    NineteenCertificate 4523 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 71
  let Q : ℤ[X] := X^17 - 70*X^16 + 4971*X^15 - 352940*X^14 + 25058741*X^13 - 1779170610*X^12
    + 126321113311*X^11 - 8968799045080*X^10 + 636784732200681*X^9 - 45211715986248350*X^8
    + 3210031835023632851*X^7 - 227912260286677932420*X^6 + 16181770480354133201821*X^5
    - 1148905704105143457329290*X^4 + 81572304991465185470379591*X^3 - 5791633654394028168396950960*X^2
    + 411205989461975999956183518161*X - 29195625251800295996889029789430
  let A : ℤ[X] := 458299666787048643771638539697
  let G : ℤ[X] := X^17 + X^14 + X^12 + X^11 + X^10 + X^8 + X^5 + X^4 + X^3 + X^2 + X
  let Qp : ℤ[X] := -62*X^17 - 183*X^16 - 638*X^15 + 6*X^14 - 488*X^13 - 1598*X^12 + 321*X^11 - 238*X^10
    - 1256*X^9 - 1346*X^8 + 521*X^7 - 869*X^6 - 1685*X^5 - 2548*X^4 - 74*X^3 + 669*X^2 - 2331*X - 1912
  let Rp : ℤ[X] := 62*X^16 + 121*X^15 + 455*X^14 - 582*X^13 + 615*X^12 + 1627*X^11 - 2380*X^10
    + 1691*X^9 + 2060*X^8 - 1462*X^7 - 227*X^6 + 2548*X^5 + 74*X^4 - 669*X^3 + 2331*X^2 - 2611*X + 4523
  let QP : ℤ[X] := -X^17 - 3*X^16 - 10*X^15 - 8*X^13 - 25*X^12 + 5*X^11 - 4*X^10 - 20*X^9 - 21*X^8
    + 8*X^7 - 14*X^6 - 27*X^5 - 40*X^4 - X^3 + 10*X^2 - 37*X - 30
  let RP : ℤ[X] := X^16 + 2*X^15 + 7*X^14 - 9*X^13 + 10*X^12 + 25*X^11 - 37*X^10 + 27*X^9 + 32*X^8
    - 23*X^7 - 3*X^6 + 40*X^5 + X^4 - 10*X^3 + 36*X^2 - 40*X + 71
  let C1 : ℤ[X] := X^16 - 71*X^15 + 5041*X^14 - 357910*X^13 + 25411610*X^12 - 1804224309*X^11
    + 128099925940*X^10 - 9095094741739*X^9 + 645751726663469*X^8 - 45848372593106298*X^7
    + 3255234454110547158*X^6 - 231121646241848848218*X^5 + 16409636883171268223479*X^4
    - 1165084218705160043867008*X^3 + 82720979528066363114557569*X^2 - 5873189546492711781133587398*X
    + 416996457800982536460484705259
  let C2 : ℤ[X] := -6545821026723360620980414343
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4561 [Fact (Nat.Prime 4561)]
    (hpn : 4561 ≠ 19)
    (hmod : 4561 % 19 = 1) :
    NineteenCertificate 4561 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 101
  let Q : ℤ[X] := X^17 - 100*X^16 + 10101*X^15 - 1020200*X^14 + 103040201*X^13 - 10407060300*X^12
    + 1051113090301*X^11 - 106162422120400*X^10 + 10722404634160401*X^9 - 1082962868050200500*X^8
    + 109379249673070250501*X^7 - 11047304216980095300600*X^6 + 1115777725914989625360601*X^5
    - 112693550317413952161420700*X^4 + 11382048582058809168303490701*X^3
    - 1149586906787939725998652560800*X^2 + 116108277585581912325863908640801*X
    - 11726936036143773144912254772720900
  let A : ℤ[X] := 259684398081675309720705488279941
  let G : ℤ[X] := -X^16 - X^15 - X^13 - X^12 - X^8 - X^5 - X^4 + X^2 - X - 1
  let Qp : ℤ[X] := 909*X^17 + 320*X^16 + 516*X^15 - 1036*X^14 + 642*X^13 - 79*X^12 - 234*X^11
    + 1738*X^10 - 1311*X^9 + 1051*X^8 - 339*X^7 - 1340*X^6 - 581*X^5 + 297*X^4 - 1722*X^3 + 1513*X^2
    - 1391*X + 9
  let Rp : ℤ[X] := 909*X^15 + 320*X^14 - 393*X^13 - 447*X^12 + 446*X^11 + 564*X^10 - 2232*X^9 + 1943*X^8
    + 789*X^7 - 2152*X^6 + 2985*X^5 - 4111*X^4 + 1069*X^3 + 1495*X^2 - 5952*X + 4570
  let QP : ℤ[X] := 20*X^17 + 7*X^16 + 11*X^15 - 23*X^14 + 14*X^13 - 2*X^12 - 5*X^11 + 38*X^10 - 29*X^9
    + 23*X^8 - 8*X^7 - 30*X^6 - 13*X^5 + 6*X^4 - 38*X^3 + 33*X^2 - 31*X
  let RP : ℤ[X] := 20*X^15 + 7*X^14 - 9*X^13 - 10*X^12 + 10*X^11 + 12*X^10 - 49*X^9 + 43*X^8 + 17*X^7
    - 47*X^6 + 65*X^5 - 91*X^4 + 24*X^3 + 32*X^2 - 131*X + 101
  let C1 : ℤ[X] := -X^15 + 100*X^14 - 10100*X^13 + 1020099*X^12 - 103030000*X^11 + 10406030000*X^10
    - 1051009030000*X^9 + 106151912030000*X^8 - 10721343115030001*X^7 + 1082855654618030101*X^6
    - 109368421116421040201*X^5 + 11046210532758525060300*X^4 - 1115667263808611031090301*X^3
    + 112682393644669714140120401*X^2 - 11380921758111641128152160500*X
    + 1149473097569275753943368210499
  let C2 : ℤ[X] := -25454238731527483259872876400
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4637 [Fact (Nat.Prime 4637)]
    (hpn : 4637 ≠ 19)
    (hmod : 4637 % 19 = 1) :
    NineteenCertificate 4637 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 56
  let Q : ℤ[X] := X^17 - 55*X^16 + 3081*X^15 - 172535*X^14 + 9661961*X^13 - 541069815*X^12
    + 30299909641*X^11 - 1696794939895*X^10 + 95020516634121*X^9 - 5321148931510775*X^8
    + 297984340164603401*X^7 - 16687123049217790455*X^6 + 934478890756196265481*X^5
    - 52330817882346990866935*X^4 + 2930525801411431488548361*X^3 - 164109444879040163358708215*X^2
    + 9190128913226249148087660041*X - 514647219140669952292908962295
  let A : ℤ[X] := 6215278040085727265128941533
  let G : ℤ[X] := -X^16 - X^15 - X^12 - X^11 - X^8 - X^5 - X^4 - X^3
  let Qp : ℤ[X] := 366*X^17 - 1582*X^16 + 855*X^15 - 1144*X^14 - 488*X^13 - 128*X^12 - 1740*X^11
    + 429*X^10 - 473*X^9 - 968*X^8 - 1070*X^7 + 5*X^6 + 86*X^5 + 187*X^4 - 832*X^3 + 588*X^2 - 103*X
    + 1497
  let Rp : ℤ[X] := 366*X^15 - 1582*X^14 + 489*X^13 + 438*X^12 - 977*X^11 - 566*X^10 - 763*X^9 + 995*X^8
    + 290*X^7 - 2329*X^6 + 588*X^5 - 103*X^4 + 1497*X^3 - 4637*X + 4637
  let QP : ℤ[X] := 4*X^17 - 19*X^16 + 10*X^15 - 14*X^14 - 6*X^13 - 2*X^12 - 21*X^11 + 5*X^10 - 6*X^9
    - 12*X^8 - 13*X^7 + X^5 + 2*X^4 - 10*X^3 + 7*X^2 - X + 18
  let RP : ℤ[X] := 4*X^15 - 19*X^14 + 6*X^13 + 5*X^12 - 12*X^11 - 7*X^10 - 9*X^9 + 12*X^8 + 3*X^7
    - 28*X^6 + 7*X^5 - X^4 + 18*X^3 - X^2 - 55*X + 56
  let C1 : ℤ[X] := -X^15 + 55*X^14 - 3080*X^13 + 172480*X^12 - 9658881*X^11 + 540897335*X^10
    - 30290250760*X^9 + 1696254042560*X^8 - 94990226383361*X^7 + 5319452677468216*X^6
    - 297889349938220096*X^5 + 16681803596540325375*X^4 - 934181001406258221001*X^3
    + 52314136078750460376055*X^2 - 2929591620410025781059080*X + 164057130742961443739308480
  let C2 : ℤ[X] := -1981280854346741610826240
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4751 [Fact (Nat.Prime 4751)]
    (hpn : 4751 ≠ 19)
    (hmod : 4751 % 19 = 1) :
    NineteenCertificate 4751 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 62
  let Q : ℤ[X] := X^17 - 61*X^16 + 3783*X^15 - 234545*X^14 + 14541791*X^13 - 901591041*X^12
    + 55898644543*X^11 - 3465715961665*X^10 + 214874389623231*X^9 - 13322212156640321*X^8
    + 825977153711699903*X^7 - 51210583530125393985*X^6 + 3175056178867774427071*X^5
    - 196853483089802014478401*X^4 + 12204915951567724897660863*X^3 - 756704788997198943654973505*X^2
    + 46915696917826334506608357311*X - 2908773208905232739409718153281
  let A : ℤ[X] := 37959153641785819794443806673
  let G : ℤ[X] := X^16 + X^14 + X^12 + X^7 + X^6 + X^5 + X^2 + 1
  let Qp : ℤ[X] := 870*X^17 - 809*X^16 - 1233*X^15 + 1300*X^14 + 1037*X^13 - 1661*X^12 - 670*X^11
    - 349*X^10 - 1247*X^9 - 2583*X^8 - 518*X^7 - 271*X^6 - 1332*X^5 - 2064*X^4 + 561*X^3 - 655*X^2
    - 1279*X - 599
  let Rp : ℤ[X] := -870*X^15 + 1679*X^14 - 446*X^13 - 854*X^12 - 183*X^11 + 1844*X^10 - 304*X^9
    - 156*X^8 + 170*X^7 + 2843*X^6 - 1349*X^5 + 2001*X^4 - 536*X^3 - 25*X^2 - 4071*X + 5350
  let QP : ℤ[X] := 11*X^17 - 11*X^16 - 16*X^15 + 17*X^14 + 13*X^13 - 22*X^12 - 9*X^11 - 5*X^10 - 17*X^9
    - 34*X^8 - 7*X^7 - 4*X^6 - 18*X^5 - 27*X^4 + 7*X^3 - 9*X^2 - 17*X - 8
  let RP : ℤ[X] := -11*X^15 + 22*X^14 - 6*X^13 - 11*X^12 - 2*X^11 + 24*X^10 - 4*X^9 - 2*X^8 + 3*X^7
    + 37*X^6 - 17*X^5 + 26*X^4 - 7*X^3 - X^2 - 52*X + 70
  let C1 : ℤ[X] := X^15 - 62*X^14 + 3845*X^13 - 238390*X^12 + 14780181*X^11 - 916371222*X^10
    + 56815015764*X^9 - 3522530977368*X^8 + 218396920596816*X^7 - 13540609077002591*X^6
    + 839517762774160643*X^5 - 52050101291997959865*X^4 + 3227106280103873511630*X^3
    - 200080589366440157721060*X^2 + 12404996540719289778705721*X - 769109785524595966279754702
  let C2 : ℤ[X] := 10036793665023142477235275
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4789 [Fact (Nat.Prime 4789)]
    (hpn : 4789 ≠ 19)
    (hmod : 4789 % 19 = 1) :
    NineteenCertificate 4789 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 188
  let Q : ℤ[X] := X^17 - 187*X^16 + 35157*X^15 - 6609515*X^14 + 1242588821*X^13 - 233606698347*X^12
    + 43918059289237*X^11 - 8256595146376555*X^10 + 1552239887518792341*X^9 - 291821098853532960107*X^8
    + 54862366584464196500117*X^7 - 10314124917879268942021995*X^6 + 1939055484561302561100135061*X^5
    - 364542431097524881486825391467*X^4 + 68533977046334677719523173595797*X^3
    - 12884387684710919411270356636009835*X^2 + 2422264884725652849318827047569848981*X
    - 455385798328422735671939484943131608427
  let A : ℤ[X] := 17876911690487257111364506821739140193
  let G : ℤ[X] := X^14 + X^8 + X^6 + X^4 + 1
  let Qp : ℤ[X] := -1019*X^17 - 1007*X^16 + 1526*X^15 - 567*X^14 + 219*X^13 + 910*X^12 + 305*X^11
    - 891*X^10 - 1126*X^9 - 47*X^8 - 1761*X^7 - 392*X^6 + 842*X^5 - 1278*X^4 - 205*X^3 - 791*X^2 - 770*X
    + 71
  let Rp : ℤ[X] := 1019*X^13 - 12*X^12 - 2533*X^11 + 2093*X^10 - 786*X^9 - 691*X^8 + 1624*X^7 + 1184*X^6
    - 1279*X^5 + 1002*X^4 - 586*X^3 + 21*X^2 - 3948*X + 4718
  let QP : ℤ[X] := -40*X^17 - 39*X^16 + 60*X^15 - 22*X^14 + 9*X^13 + 36*X^12 + 12*X^11 - 35*X^10
    - 44*X^9 - 2*X^8 - 69*X^7 - 15*X^6 + 33*X^5 - 50*X^4 - 8*X^3 - 31*X^2 - 30*X + 3
  let RP : ℤ[X] := 40*X^13 - X^12 - 99*X^11 + 82*X^10 - 31*X^9 - 27*X^8 + 64*X^7 + 46*X^6 - 50*X^5
    + 39*X^4 - 23*X^3 - 154*X + 185
  let C1 : ℤ[X] := X^13 - 188*X^12 + 35344*X^11 - 6644672*X^10 + 1249198336*X^9 - 234849287168*X^8
    + 44151665987585*X^7 - 8300513205665980*X^6 + 1560496482665204241*X^5 - 293373338741058397308*X^4
    + 55154187683318978693905*X^3 - 10368987284463967994454140*X^2 + 1949369609479225982957378320*X
    - 366481486582094484795987124160
  let C2 : ℤ[X] := 14386828038720769083659548829
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_4903 [Fact (Nat.Prime 4903)]
    (hpn : 4903 ≠ 19)
    (hmod : 4903 % 19 = 1) :
    NineteenCertificate 4903 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 373
  let Q : ℤ[X] := X^17 - 372*X^16 + 138757*X^15 - 51756360*X^14 + 19305122281*X^13 - 7200810610812*X^12
    + 2685902357832877*X^11 - 1001841579471663120*X^10 + 373686909142930343761*X^9
    - 139385217110313018222852*X^8 + 51990685982146755797123797*X^7 - 19392525871340739912327176280*X^6
    + 7233412150010095987298036752441*X^5 - 2698062731953765803262167708660492*X^4
    + 1006377399018754644616788555330363517*X^3 - 375378769833995482442062131138225591840*X^2
    + 140016281148080314950889174914558145756321*X - 52226072868233957476681662243130188367107732
  let A : ℤ[X] := 3973144030155265376055937184721101419728979
  let G : ℤ[X] := X^17 + X^10 + X^9 + X^8 + X^7 + X^6 + X^5 + 2*X^4 + X^3 + X^2 + X + 1
  let Qp : ℤ[X] := -972*X^17 - 1238*X^16 - 80*X^15 - 550*X^14 - 1748*X^13 - 1067*X^12 - 124*X^11
    + 1153*X^10 + 423*X^9 - 1855*X^8 - 380*X^7 - 1419*X^6 - 1209*X^5 - 1091*X^4 - 978*X^3 + 1000*X^2
    - 1344*X + 234
  let Rp : ℤ[X] := 972*X^16 + 266*X^15 - 1158*X^14 + 470*X^13 + 1198*X^12 - 681*X^11 - 943*X^10
    - 305*X^9 + 1968*X^8 + 2358*X^7 - 925*X^6 + 2787*X^5 + 857*X^4 + 978*X^3 - 1000*X^2 - 3559*X + 4669
  let QP : ℤ[X] := -74*X^17 - 94*X^16 - 6*X^15 - 42*X^14 - 133*X^13 - 81*X^12 - 9*X^11 + 88*X^10
    + 32*X^9 - 141*X^8 - 29*X^7 - 108*X^6 - 92*X^5 - 83*X^4 - 74*X^3 + 76*X^2 - 102*X + 18
  let RP : ℤ[X] := 74*X^16 + 20*X^15 - 88*X^14 + 36*X^13 + 91*X^12 - 52*X^11 - 72*X^10 - 23*X^9
    + 150*X^8 + 179*X^7 - 70*X^6 + 212*X^5 + 65*X^4 + 74*X^3 - 77*X^2 - 270*X + 355
  let C1 : ℤ[X] := X^16 - 373*X^15 + 139129*X^14 - 51895117*X^13 + 19356878641*X^12 - 7220115733093*X^11
    + 2693103168443689*X^10 - 1004527481829495996*X^9 + 374688750722402006509*X^8
    - 139758904019455948427856*X^7 + 52130071199257068763590289*X^6 - 19444516557322886648819177796*X^5
    + 7252804675881436720009553317909*X^4 - 2705296144103775896563563387580055*X^3
    + 1009075461750708409418209143567360516*X^2 - 376385147233014236712992010550625472467*X
    + 140391659917914310293946019935383301230192
  let C2 : ℤ[X] := -10680417937871107024197810613073214635705
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_5701 [Fact (Nat.Prime 5701)]
    (hpn : 5701 ≠ 19)
    (hmod : 5701 % 19 = 1) :
    NineteenCertificate 5701 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 278
  let Q : ℤ[X] := X^17 - 277*X^16 + 77007*X^15 - 21407945*X^14 + 5951408711*X^13 - 1654491621657*X^12
    + 459948670820647*X^11 - 127865730488139865*X^10 + 35546673075702882471*X^9
    - 9881975115045401326937*X^8 + 2747189081982621568888487*X^7 - 763718564791168796150999385*X^6
    + 212313761011944925329977829031*X^5 - 59023225561320689241733836470617*X^4
    + 16408456706047151609202006538831527*X^3 - 4561550964281108147358157817795164505*X^2
    + 1268111168070148064965567873347055732391*X - 352534904723501162060427868790481493604697
  let A : ℤ[X] := 17190791705513650772285379323584258063867
  let G : ℤ[X] := X^10 + X^9 + X^4 + X^3 + X
  let Qp : ℤ[X] := -3468*X^17 - 2833*X^16 - 2632*X^15 - 1500*X^14 - 2641*X^13 - 4699*X^12 - 2675*X^11
    - 948*X^10 - 2170*X^9 - 4514*X^8 - 2796*X^7 - 1516*X^6 - 3894*X^5 - 4126*X^4 - 2341*X^3 - 2584*X^2
    - 3442*X - 4360
  let Rp : ℤ[X] := 3468*X^9 + 2833*X^8 - 836*X^7 - 1333*X^6 + 9*X^5 + 3199*X^4 + 3502*X^3 - 918*X^2
    - 1341*X + 5701
  let QP : ℤ[X] := -169*X^17 - 138*X^16 - 128*X^15 - 73*X^14 - 129*X^13 - 229*X^12 - 130*X^11 - 46*X^10
    - 106*X^9 - 220*X^8 - 136*X^7 - 74*X^6 - 190*X^5 - 201*X^4 - 114*X^3 - 126*X^2 - 168*X - 212
  let RP : ℤ[X] := 169*X^9 + 138*X^8 - 41*X^7 - 65*X^6 + X^5 + 156*X^4 + 170*X^3 - 45*X^2 - 65*X + 278
  let C1 : ℤ[X] := X^9 - 277*X^8 + 77006*X^7 - 21407668*X^6 + 5951331704*X^5 - 1654470213712*X^4
    + 459942719411937*X^3 - 127864075996518485*X^2 + 35546213127032138830*X - 9881847249314934594739
  let C2 : ℤ[X] := 481872221594378498042
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_6043 [Fact (Nat.Prime 6043)]
    (hpn : 6043 ≠ 19)
    (hmod : 6043 % 19 = 1) :
    NineteenCertificate 6043 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 446
  let Q : ℤ[X] := X^17 - 445*X^16 + 198471*X^15 - 88518065*X^14 + 39479056991*X^13 - 17607659417985*X^12
    + 7853016100421311*X^11 - 3502445180787904705*X^10 + 1562090550631405498431*X^9
    - 696692385581606852300225*X^8 + 310724803969396656125900351*X^7
    - 138583262570350908632151556545*X^6 + 61808135106376505249939594219071*X^5
    - 27566428257443921341473059021705665*X^4 + 12294627002819988918296984323680726591*X^3
    - 5483403643257715057560455008361604059585*X^2 + 2445598024892940915671962933729275410574911*X
    - 1090736719102251648389695468443256833116410305
  let A : ℤ[X] := 80501171060665933341354323833475516725123117
  let G : ℤ[X] := -X^17 - X^16 - X^13 - X^10 - X^9 + X^7 - X^6 - X^5 - X^2 + 1
  let Qp : ℤ[X] := -2606*X^17 - 586*X^16 - 1099*X^15 - 1935*X^14 - 3745*X^13 - 204*X^12 - 2267*X^11
    - 705*X^10 - 2412*X^9 - 2508*X^8 - 1993*X^7 - 2049*X^6 - 1245*X^5 - 3292*X^4 - 2823*X^3 - 492*X^2
    - 722*X - 873
  let Rp : ℤ[X] := -2606*X^16 - 586*X^15 + 1507*X^14 - 1349*X^13 - 5252*X^12 + 3751*X^11 + 965*X^10
    - 3943*X^9 - 2541*X^8 + 3245*X^7 - 387*X^6 - 5251*X^5 + 699*X^4 + 2482*X^3 - 1103*X^2 - 6194*X
    + 6916
  let QP : ℤ[X] := -192*X^17 - 43*X^16 - 81*X^15 - 143*X^14 - 276*X^13 - 15*X^12 - 167*X^11 - 52*X^10
    - 178*X^9 - 185*X^8 - 147*X^7 - 151*X^6 - 92*X^5 - 243*X^4 - 208*X^3 - 36*X^2 - 53*X - 64
  let RP : ℤ[X] := -192*X^16 - 43*X^15 + 111*X^14 - 100*X^13 - 387*X^12 + 277*X^11 + 71*X^10 - 291*X^9
    - 187*X^8 + 239*X^7 - 29*X^6 - 387*X^5 + 52*X^4 + 183*X^3 - 82*X^2 - 456*X + 510
  let C1 : ℤ[X] := -X^16 + 445*X^15 - 198470*X^14 + 88517620*X^13 - 39478858521*X^12
    + 17607570900366*X^11 - 7852976621563236*X^10 + 3502427573217203255*X^9 - 1562082697654872651731*X^8
    + 696688883154073202672026*X^7 - 310723241886716648391723595*X^6
    + 138582565881475625182708723369*X^5 - 61807824383138128831488090622575*X^4
    + 27566289674879605458843688417668450*X^3 - 12294565194996304034644285034280128700*X^2
    + 5483376076968351599451351125288937400199*X - 2445585730327884813355302601878866080488754
  let C2 : ℤ[X] := 180494991846142086175155545331453627651495
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_6271 [Fact (Nat.Prime 6271)]
    (hpn : 6271 ≠ 19)
    (hmod : 6271 % 19 = 1) :
    NineteenCertificate 6271 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 301
  let Q : ℤ[X] := X^17 - 300*X^16 + 90301*X^15 - 27180600*X^14 + 8181360601*X^13 - 2462589540900*X^12
    + 741239451810901*X^11 - 223113074995081200*X^10 + 67157035573519441201*X^9
    - 20214267707629351801500*X^8 + 6084494579996434892251501*X^7 - 1831432868578926902567701800*X^6
    + 551261293442256997672878241801*X^5 - 165929649326119356299536350782100*X^4
    + 49944824447161926246160441585412101*X^3 - 15033392158595739800094292917209042400*X^2
    + 4525051039737317679828382168079921762401*X - 1362040362960932621628343032592056450482700
  let A : ℤ[X] := 65376199848706860007994140138767180927331
  let G : ℤ[X] := -X^17 - X^14 - X^7 - X^5 - X^4 - 1
  let Qp : ℤ[X] := 1425*X^17 - 1072*X^16 - 1995*X^15 - 96*X^14 - 1034*X^13 - 891*X^12 - 37*X^11
    + 20*X^10 + 1676*X^9 - 1371*X^8 + 210*X^7 + 925*X^6 - 1076*X^5 - 791*X^4 + 1218*X^3 - 1475*X^2
    + 159*X - 2537
  let Rp : ℤ[X] := 1425*X^16 - 2497*X^15 - 923*X^14 + 3324*X^13 - 3435*X^12 - 780*X^11 + 2753*X^10
    - 881*X^9 + 1799*X^8 - 2193*X^7 + 3063*X^6 - 126*X^5 - 4546*X^4 + 2693*X^3 - 1634*X^2 - 3575*X
    + 3734
  let QP : ℤ[X] := 68*X^17 - 52*X^16 - 96*X^15 - 5*X^14 - 50*X^13 - 43*X^12 - 2*X^11 + X^10 + 80*X^9
    - 66*X^8 + 10*X^7 + 44*X^6 - 52*X^5 - 38*X^4 + 58*X^3 - 71*X^2 + 7*X - 122
  let RP : ℤ[X] := 68*X^16 - 120*X^15 - 44*X^14 + 159*X^13 - 165*X^12 - 37*X^11 + 132*X^10 - 42*X^9
    + 86*X^8 - 105*X^7 + 147*X^6 - 7*X^5 - 218*X^4 + 129*X^3 - 79*X^2 - 171*X + 179
  let C1 : ℤ[X] := -X^16 + 301*X^15 - 90601*X^14 + 27270900*X^13 - 8208540900*X^12 + 2470770810900*X^11
    - 743702014080900*X^10 + 223854306238350900*X^9 - 67380146177743620900*X^8
    + 20281423999500829890900*X^7 - 6104708623849749797160901*X^6 + 1837517295778774688945431201*X^5
    - 553092706029411181372574791502*X^4 + 166480904514852765593145012242101*X^3
    - 50110752258970682443536648684872401*X^2 + 15083336429950175415504531254146592701*X
    - 4540084265415002800066863907498124403001
  let C2 : ℤ[X] := 217918252892667173149438053923925282300
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_6689 [Fact (Nat.Prime 6689)]
    (hpn : 6689 ≠ 19)
    (hmod : 6689 % 19 = 1) :
    NineteenCertificate 6689 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 44
  let Q : ℤ[X] := X^17 - 43*X^16 + 1893*X^15 - 83291*X^14 + 3664805*X^13 - 161251419*X^12
    + 7095062437*X^11 - 312182747227*X^10 + 13736040877989*X^9 - 604385798631515*X^8
    + 26592975139786661*X^7 - 1170090906150613083*X^6 + 51483999870626975653*X^5
    - 2265295994307586928731*X^4 + 99673023749533824864165*X^3 - 4385613044979488294023259*X^2
    + 192966973979097484937023397*X - 8490546855080289337229029467
  let A : ℤ[X] := 55850510034912951239060741
  let G : ℤ[X] := X^15 + X^14 + X^13 + X^12 + X^8 + X^7 + X
  let Qp : ℤ[X] := -2177*X^17 - 35*X^16 - 637*X^15 - 905*X^14 - 2491*X^13 + 403*X^12 + 158*X^11
    - 2440*X^10 - 1841*X^9 - 1441*X^8 + 1026*X^7 - 498*X^6 - 332*X^5 - 947*X^4 - 643*X^3 - 641*X^2
    - 729*X - 3546
  let Rp : ℤ[X] := 2177*X^14 + 35*X^13 + 637*X^12 + 905*X^11 + 314*X^10 - 438*X^9 - 795*X^8 + 3712*X^7
    - 615*X^6 + 304*X^5 + 2*X^4 - 88*X^3 - 2817*X^2 - 3143*X + 6689
  let QP : ℤ[X] := -14*X^17 - 4*X^15 - 6*X^14 - 16*X^13 + 3*X^12 + X^11 - 16*X^10 - 12*X^9 - 9*X^8
    + 7*X^7 - 3*X^6 - 2*X^5 - 6*X^4 - 4*X^3 - 4*X^2 - 5*X - 23
  let RP : ℤ[X] := 14*X^14 + 4*X^12 + 6*X^11 + 2*X^10 - 3*X^9 - 5*X^8 + 24*X^7 - 4*X^6 + 2*X^5 - X^3
    - 19*X^2 - 20*X + 44
  let C1 : ℤ[X] := X^14 - 43*X^13 + 1893*X^12 - 83291*X^11 + 3664804*X^10 - 161251376*X^9
    + 7095060544*X^8 - 312182663935*X^7 + 13736037213141*X^6 - 604385637378204*X^5
    + 26592968044640976*X^4 - 1170090593964202944*X^3 + 51483986134424929536*X^2
    - 2265295389914696899584*X + 99672997156246663581697
  let C2 : ℤ[X] := -655645369244259709612
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_6803 [Fact (Nat.Prime 6803)]
    (hpn : 6803 ≠ 19)
    (hmod : 6803 % 19 = 1) :
    NineteenCertificate 6803 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 439
  let Q : ℤ[X] := X^17 - 438*X^16 + 192283*X^15 - 84412236*X^14 + 37056971605*X^13 - 16268010534594*X^12
    + 7141656624686767*X^11 - 3135187258237490712*X^10 + 1376347206366258422569*X^9
    - 604216423594787447507790*X^8 + 265251009958111689455919811*X^7
    - 116445193371611031671148797028*X^6 + 51119439890137242903634321895293*X^5
    - 22441434111770249634695467312033626*X^4 + 9851789575067139589631310149982761815*X^3
    - 4324935623454474279848145155842432436784*X^2 + 1898646738696514208853335723414827839748177*X
    - 833505918287769737686614382579109421649449702
  let A : ℤ[X] := 53786432181145217528211629274177427032795593
  let G : ℤ[X] := X^16 - X^13 + X^11 + X^10 + X^5
  let Qp : ℤ[X] := -325*X^17 - 513*X^16 + 383*X^15 + 1613*X^14 - 920*X^13 + 2178*X^12 + 2756*X^11
    + 725*X^10 + 1141*X^9 + 2198*X^8 + 779*X^7 - 2156*X^6 + 542*X^5 - 158*X^4 + 1007*X^3 - 203*X^2
    + 353*X + 1177
  let Rp : ℤ[X] := 325*X^15 + 188*X^14 - 896*X^13 - 1555*X^12 + 2345*X^11 - 1877*X^10 + 1165*X^9
    - 1210*X^8 + 556*X^7 + 824*X^6 - 1177*X^5 - 6803*X + 6803
  let QP : ℤ[X] := -21*X^17 - 33*X^16 + 25*X^15 + 104*X^14 - 59*X^13 + 141*X^12 + 178*X^11 + 47*X^10
    + 74*X^9 + 142*X^8 + 50*X^7 - 139*X^6 + 35*X^5 - 10*X^4 + 65*X^3 - 13*X^2 + 23*X + 76
  let RP : ℤ[X] := 21*X^15 + 12*X^14 - 58*X^13 - 100*X^12 + 151*X^11 - 121*X^10 + 75*X^9 - 78*X^8
    + 36*X^7 + 53*X^6 - 76*X^5 - X^2 - 438*X + 439
  let C1 : ℤ[X] := X^15 - 439*X^14 + 192721*X^13 - 84604520*X^12 + 37141384280*X^11
    - 16305067698919*X^10 + 7157924719825442*X^9 - 3142328952003369038*X^8 + 1379482409929479007682*X^7
    - 605592777959041284372398*X^6 + 265855229524019123839482722*X^5
    - 116710445761044395365532914957*X^4 + 51235885689098489565468949666123*X^3
    - 22492553817514236919240868903427997*X^2 + 9874231125888750007546741448604890683*X
    - 4334787464265161253313019495937547009837
  let C2 : ℤ[X] := 279725370691225310922301272779153775881
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_6841 [Fact (Nat.Prime 6841)]
    (hpn : 6841 ≠ 19)
    (hmod : 6841 % 19 = 1) :
    NineteenCertificate 6841 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 339
  let Q : ℤ[X] := X^17 - 338*X^16 + 114583*X^15 - 38843636*X^14 + 13167992605*X^13 - 4463949493094*X^12
    + 1513278878158867*X^11 - 513001539695855912*X^10 + 173907521956895154169*X^9
    - 58954649943387457263290*X^8 + 19985626330808348012255311*X^7 - 6775127326144029976154550428*X^6
    + 2296768163562826161916392595093*X^5 - 778604407447798068889657089736526*X^4
    + 263946894124803545353593753420682315*X^3 - 89477997108308401874868282409611304784*X^2
    + 30333041019716548235580347736858232321777*X - 10282900905683909851861737882794940757082402
  let A : ℤ[X] := 509560503877626873232148683272545668272319
  let G : ℤ[X] := -X^14 - X^13 + X^9 - X^4 + X^3
  let Qp : ℤ[X] := 6495*X^17 + 7492*X^16 - 2123*X^15 + 1046*X^14 + 7633*X^13 + 4806*X^12 - 1422*X^11
    + 2842*X^10 + 7638*X^9 + 3111*X^8 - 1461*X^7 + 2381*X^6 + 6574*X^5 + 1234*X^4 - 1371*X^3 + 6076*X^2
    + 5872*X - 223
  let Rp : ℤ[X] := 6495*X^13 + 7492*X^12 - 8618*X^11 - 6446*X^10 + 9756*X^9 - 2735*X^8 - 10052*X^7
    + 7651*X^6 + 5891*X^5 - 6318*X^4 + 223*X^3 - 6841*X + 6841
  let QP : ℤ[X] := 322*X^17 + 370*X^16 - 106*X^15 + 52*X^14 + 378*X^13 + 237*X^12 - 71*X^11 + 141*X^10
    + 378*X^9 + 153*X^8 - 73*X^7 + 118*X^6 + 325*X^5 + 60*X^4 - 68*X^3 + 301*X^2 + 290*X - 12
  let RP : ℤ[X] := 322*X^13 + 370*X^12 - 428*X^11 - 318*X^10 + 484*X^9 - 137*X^8 - 497*X^7 + 380*X^6
    + 291*X^5 - 314*X^4 + 12*X^3 - X^2 - 338*X + 339
  let C1 : ℤ[X] := -X^13 + 338*X^12 - 114582*X^11 + 38843298*X^10 - 13167878022*X^9 + 4463910649459*X^8
    - 1513265710166601*X^7 + 512997075746477739*X^6 - 173906008678055953521*X^5
    + 58954136941860968243619*X^4 - 19985452423290868234586842*X^3 + 6775068371495604331524939439*X^2
    - 2296748177937009868386954469821*X + 778597632320646345383177565269319
  let C2 : ℤ[X] := -38582750673395572443341206640301
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_6917 [Fact (Nat.Prime 6917)]
    (hpn : 6917 ≠ 19)
    (hmod : 6917 % 19 = 1) :
    NineteenCertificate 6917 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 114
  let Q : ℤ[X] := X^17 - 113*X^16 + 12883*X^15 - 1468661*X^14 + 167427355*X^13 - 19086718469*X^12
    + 2175885905467*X^11 - 248050993223237*X^10 + 28277813227449019*X^9 - 3223670707929188165*X^8
    + 367498460703927450811*X^7 - 41894824520247729392453*X^6 + 4776009995308241150739643*X^5
    - 544465139465139491184319301*X^4 + 62069025899025901995012400315*X^3
    - 7075868952488952827431413635909*X^2 + 806649060583740622327181154493627*X
    - 91957992906546430945298651612273477
  let A : ℤ[X] := 1515571951907805859153396889373887
  let G : ℤ[X] := X^15 - X^10 - X^7 - X^4 + X^2
  let Qp : ℤ[X] := -303*X^17 - 346*X^16 - 2361*X^15 - 912*X^14 - 90*X^13 - 3877*X^12 - 1013*X^11
    - 2410*X^10 - 2243*X^9 - 530*X^8 - 2136*X^7 + 1106*X^6 - 1881*X^5 - 296*X^4 - 1144*X^3 - 1310*X^2
    - 3137*X - 2369
  let Rp : ℤ[X] := 303*X^14 + 43*X^13 + 2015*X^12 - 1449*X^11 - 822*X^10 + 3484*X^9 - 2907*X^8 - 618*X^7
    + 979*X^6 - 934*X^5 - 4196*X^4 + 768*X^3 + 2369*X^2 - 6917*X + 6917
  let QP : ℤ[X] := -5*X^17 - 6*X^16 - 39*X^15 - 15*X^14 - 2*X^13 - 64*X^12 - 17*X^11 - 40*X^10 - 37*X^9
    - 9*X^8 - 35*X^7 + 18*X^6 - 31*X^5 - 5*X^4 - 19*X^3 - 22*X^2 - 52*X - 39
  let RP : ℤ[X] := 5*X^14 + X^13 + 33*X^12 - 24*X^11 - 13*X^10 + 57*X^9 - 48*X^8 - 10*X^7 + 16*X^6
    - 16*X^5 - 69*X^4 + 13*X^3 + 38*X^2 - 113*X + 114
  let C1 : ℤ[X] := X^14 - 114*X^13 + 12996*X^12 - 1481544*X^11 + 168896016*X^10 - 19254145825*X^9
    + 2194972624050*X^8 - 250226879141700*X^7 + 28525864222153799*X^6 - 3251948521325533086*X^5
    + 370722131431110771804*X^4 - 42262322983146627985657*X^3 + 4817904820078715590364898*X^2
    - 549241149488973577301598371*X + 62613491041742987812382214294
  let C2 : ℤ[X] := -1031941300962657309615667548
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_7069 [Fact (Nat.Prime 7069)]
    (hpn : 7069 ≠ 19)
    (hmod : 7069 % 19 = 1) :
    NineteenCertificate 7069 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 637
  let Q : ℤ[X] := X^17 - 636*X^16 + 405133*X^15 - 258069720*X^14 + 164390411641*X^13
    - 104716692215316*X^12 + 66704532941156293*X^11 - 42490787483516558640*X^10
    + 27066631627000047853681*X^9 - 17241444346399030482794796*X^8 + 10982800048656182417540285053*X^7
    - 6996043630993988199973161578760*X^6 + 4456479792943170483382903925670121*X^5
    - 2838777628104799597914909800651867076*X^4 + 1808301349102757343871797543015239327413*X^3
    - 1151887959378456428046335034900707451562080*X^2 + 733752630124076744665515417231750646645044961*X
    - 467400425389036886351933320776625161912893640156
  let A : ℤ[X] := 42118272877750247079669193002505337125267116817
  let G : ℤ[X] := X^17 + X^15 + X^11 + X^10 + X^7 + X^6 + X^5 + X + 1
  let Qp : ℤ[X] := -2323*X^17 + 7*X^16 + 287*X^15 - 1348*X^14 + 1004*X^13 + 1408*X^12 - 1456*X^11
    - 890*X^10 - 913*X^9 - 400*X^8 - 2007*X^7 - 3353*X^6 - 1300*X^5 - 1296*X^4 - 3844*X^3 + 431*X^2
    - 1179*X - 614
  let Rp : ℤ[X] := 2323*X^16 - 2330*X^15 + 2043*X^14 - 695*X^13 - 2632*X^12 + 1231*X^11 + 2835*X^10
    - 977*X^9 + 277*X^8 + 276*X^7 + 3236*X^6 - 1930*X^5 + 1727*X^4 + 2665*X^3 - 1045*X^2 - 5890*X + 7683
  let QP : ℤ[X] := -209*X^17 + X^16 + 26*X^15 - 121*X^14 + 91*X^13 + 127*X^12 - 131*X^11 - 80*X^10
    - 82*X^9 - 36*X^8 - 181*X^7 - 302*X^6 - 117*X^5 - 117*X^4 - 346*X^3 + 39*X^2 - 106*X - 55
  let RP : ℤ[X] := 209*X^16 - 210*X^15 + 184*X^14 - 63*X^13 - 237*X^12 + 111*X^11 + 255*X^10 - 88*X^9
    + 25*X^8 + 25*X^7 + 291*X^6 - 174*X^5 + 156*X^4 + 240*X^3 - 95*X^2 - 530*X + 692
  let C1 : ℤ[X] := X^16 - 637*X^15 + 405770*X^14 - 258475490*X^13 + 164648887130*X^12
    - 104881341101810*X^11 + 66809414281852971*X^10 - 42557596897540342526*X^9
    + 27109189223733198189062*X^8 - 17268553535518047246432494*X^7 + 11000068602124996095977498679*X^6
    - 7007043699553622513137666658522*X^5 + 4463486836615657540868693661478515*X^4
    - 2843241114924173853533357862361814055*X^3 + 1811144590206698744700748958324475553035*X^2
    - 1153699103961667100374377086452690927283295*X + 734906329223581942938478204070364120679458916
  let C2 : ℤ[X] := -66223699492915786907880975525933221795560239
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem nineteenCertificate_7297 [Fact (Nat.Prime 7297)]
    (hpn : 7297 ≠ 19)
    (hmod : 7297 % 19 = 1) :
    NineteenCertificate 7297 hpn := by
  dsimp only [NineteenCertificate]
  let P : ℤ[X] := X + 39
  let Q : ℤ[X] := X^17 - 38*X^16 + 1483*X^15 - 57836*X^14 + 2255605*X^13 - 87968594*X^12
    + 3430775167*X^11 - 133800231512*X^10 + 5218209028969*X^9 - 203510152129790*X^8
    + 7936895933061811*X^7 - 309538941389410628*X^6 + 12072018714187014493*X^5
    - 470808729853293565226*X^4 + 18361540464278449043815*X^3 - 716100078106859512708784*X^2
    + 27927903046167520995642577*X - 1089188218800533318830060502
  let A : ℤ[X] := 5821343090752473541780507
  let G : ℤ[X] := X^9 - X^8 - X^5 + X^4 - X^2 - 1
  let Qp : ℤ[X] := 2531*X^17 + 5980*X^16 + 2815*X^15 + 2201*X^14 + 4256*X^13 + 4378*X^12 - 380*X^11
    + 2757*X^10 + 4463*X^9 + 3602*X^8 + 696*X^7 + 4575*X^6 + 6531*X^5 + 3217*X^4 + 1117*X^3 + 2750*X^2
    + 4736*X + 252
  let Rp : ℤ[X] := -2531*X^8 - 918*X^7 + 6614*X^6 - 2551*X^5 - 138*X^4 + 2851*X^3 - 1734*X^2 - 2813*X + 7549
  let QP : ℤ[X] := 14*X^17 + 32*X^16 + 15*X^15 + 12*X^14 + 23*X^13 + 23*X^12 - 2*X^11 + 15*X^10 + 24*X^9
    + 19*X^8 + 4*X^7 + 25*X^6 + 35*X^5 + 17*X^4 + 6*X^3 + 15*X^2 + 25*X + 1
  let RP : ℤ[X] := -14*X^8 - 4*X^7 + 35*X^6 - 14*X^5 + 15*X^3 - 10*X^2 - 14*X + 40
  let C1 : ℤ[X] := X^8 - 40*X^7 + 1560*X^6 - 60840*X^5 + 2372759*X^4 - 92537600*X^3 + 3608966400*X^2
    - 140749689601*X + 5489237894439
  let C2 : ℤ[X] := -29338122226
  let d := 1
  use P, Q, A, G, Qp, Rp, QP, RP, C1, C2
  rw [show P.natDegree = d by
    simp only [P]
    compute_degree!]
  refine ⟨by simp only [P]; monicity!, ?_, ?_, ?_⟩
  · exact NineteenCertificateArithmetic.orderOf_unitOfCoprime_eq_one_of_mod_eq_one
      hpn hmod
  · simp only [P, Q, A]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    ring
  · simp only [P, G, Qp, Rp, QP, RP, C1, C2]
    rw [NineteenCertificateArithmetic.cyclotomic_19]
    refine ⟨?_, ?_, ?_⟩ <;> ring
