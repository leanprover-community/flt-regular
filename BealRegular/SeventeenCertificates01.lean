import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 647 through 1531. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_647 [Fact (Nat.Prime 647)]
    (hpn : 647 ≠ 17)
    (hmod : 647 % 17 = 1) : SeventeenCertificate 647 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 40
  let Q : ℤ[X] := X^15 - 39*X^14 + 1561*X^13 - 62439*X^12 + 2497561*X^11 - 99902439*X^10
    + 3996097561*X^9 - 159843902439*X^8 + 6393756097561*X^7 - 255750243902439*X^6
    + 10230009756097561*X^5 - 409200390243902439*X^4 + 16368015609756097561*X^3
    - 654720624390243902439*X^2 + 26188824975609756097561*X - 1047552999024390243902439
  let A : ℤ[X] := 64763709367813925434463
  let G : ℤ[X] := X^9 + X^7 + X^6 + X^4 + X^3 + X^2 + X + 1
  let Qp : ℤ[X] := -217*X^15 - 595*X^14 - 356*X^13 - 211*X^12 - 188*X^11 - 461*X^10 - 540*X^9 + 32*X^8
    - 203*X^7 - 508*X^6 - 601*X^5 - 116*X^4 - 106*X^3 - 506*X^2 - 681*X - 151
  let Rp : ℤ[X] := 217*X^8 + 378*X^7 - 22*X^6 + 450*X^5 + 116*X^4 + 106*X^3 + 506*X^2 + 34*X + 798
  let QP : ℤ[X] := -14*X^15 - 37*X^14 - 22*X^13 - 13*X^12 - 12*X^11 - 29*X^10 - 33*X^9 + 2*X^8 - 13*X^7
    - 32*X^6 - 37*X^5 - 7*X^4 - 7*X^3 - 32*X^2 - 42*X - 9
  let RP : ℤ[X] := 14*X^8 + 23*X^7 - X^6 + 28*X^5 + 7*X^4 + 7*X^3 + 31*X^2 + 3*X + 49
  let C1 : ℤ[X] := X^8 - 40*X^7 + 1601*X^6 - 64039*X^5 + 2561560*X^4 - 102462399*X^3 + 4098495961*X^2
    - 163939838439*X + 6557593537561
  let C2 : ℤ[X] := -405415365537
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
theorem seventeenCertificate_919 [Fact (Nat.Prime 919)]
    (hpn : 919 ≠ 17)
    (hmod : 919 % 17 = 1) : SeventeenCertificate 919 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 70
  let Q : ℤ[X] := X^15 - 69*X^14 + 4831*X^13 - 338169*X^12 + 23671831*X^11 - 1657028169*X^10
    + 115991971831*X^9 - 8119438028169*X^8 + 568360661971831*X^7 - 39785246338028169*X^6
    + 2784967243661971831*X^5 - 194947707056338028169*X^4 + 13646339493943661971831*X^3
    - 955243764576056338028169*X^2 + 66867063520323943661971831*X - 4680694446422676056338028169
  let A : ℤ[X] := 356527324537091756195497249
  let G : ℤ[X] := X^15 + X^14 + X^13 + X^12 + X^9 + X^8 + X^7 + X^6 + X^2 + 1
  let Qp : ℤ[X] := -390*X^15 - 660*X^14 - 140*X^13 + 220*X^12 - 167*X^11 - 647*X^10 - 131*X^9 + 509*X^8
    - 179*X^7 - 726*X^6 - 115*X^5 + 308*X^4 + 106*X^3 - 458*X^2 - 495*X + 257
  let Rp : ℤ[X] := 390*X^14 + 660*X^13 + 140*X^12 - 220*X^11 - 223*X^10 - 13*X^9 + 381*X^8 + 371*X^7
    + 152*X^6 - 141*X^5 - 239*X^4 + 188*X^3 - 294*X^2 - 167*X + 662
  let QP : ℤ[X] := -30*X^15 - 50*X^14 - 10*X^13 + 17*X^12 - 13*X^11 - 49*X^10 - 9*X^9 + 39*X^8 - 14*X^7
    - 55*X^6 - 8*X^5 + 24*X^4 + 8*X^3 - 35*X^2 - 37*X + 20
  let RP : ℤ[X] := 30*X^14 + 50*X^13 + 10*X^12 - 17*X^11 - 17*X^10 - X^9 + 29*X^8 + 28*X^7 + 11*X^6
    - 11*X^5 - 18*X^4 + 14*X^3 - 23*X^2 - 12*X + 50
  let C1 : ℤ[X] := X^14 - 69*X^13 + 4831*X^12 - 338169*X^11 + 23671830*X^10 - 1657028100*X^9
    + 115991967001*X^8 - 8119437690069*X^7 + 568360638304831*X^6 - 39785244681338169*X^5
    + 2784967127693671830*X^4 - 194947698938557028100*X^3 + 13646338925698991967000*X^2
    - 955243724798929437689999*X + 66867060735925060638299930
  let C2 : ℤ[X] := -5093247281300059025768221
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
theorem seventeenCertificate_953 [Fact (Nat.Prime 953)]
    (hpn : 953 ≠ 17)
    (hmod : 953 % 17 = 1) : SeventeenCertificate 953 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 4
  let Q : ℤ[X] := X^15 - 3*X^14 + 13*X^13 - 51*X^12 + 205*X^11 - 819*X^10 + 3277*X^9 - 13107*X^8
    + 52429*X^7 - 209715*X^6 + 838861*X^5 - 3355443*X^4 + 13421773*X^3 - 53687091*X^2 + 214748365*X
    - 858993459
  let A : ℤ[X] := 3605429
  let G : ℤ[X] := -X^15 - X^14 - 2*X^13 - X^11 - X^10 - 2*X^9 - X^6 - X^5 - X^4 - X^2 - X - 1
  let Qp : ℤ[X] := 51*X^15 - 153*X^14 - 290*X^13 + 258*X^12 - 28*X^11 + 163*X^10 + 352*X^9 - 404*X^8
    - 239*X^7 + 54*X^6 - 165*X^5 - 242*X^4 + 66*X^3 - 213*X^2 - 50*X + 251
  let Rp : ℤ[X] := 51*X^14 - 153*X^13 - 239*X^12 + 3*X^11 + 39*X^10 + 848*X^9 - 431*X^8 - 182*X^7
    - 225*X^6 - 2*X^5 + 59*X^4 - 185*X^3 - 213*X^2 - 1003*X + 1204
  let QP : ℤ[X] := -X^14 - X^13 + X^12 + X^10 + X^9 - 2*X^8 - X^7 - X^5 - X^4 - X^2 + 1
  let RP : ℤ[X] := -X^13 - X^12 + X^10 + 3*X^9 - 2*X^8 - X^7 - X^6 - X^3 - 2*X^2 - 3*X + 5
  let C1 : ℤ[X] := -X^14 + 3*X^13 - 14*X^12 + 56*X^11 - 225*X^10 + 899*X^9 - 3598*X^8 + 14392*X^7
    - 57568*X^6 + 230271*X^5 - 921085*X^4 + 3684339*X^3 - 14737356*X^2 + 58949423*X - 235797693
  let C2 : ℤ[X] := 989707
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
theorem seventeenCertificate_1021 [Fact (Nat.Prime 1021)]
    (hpn : 1021 ≠ 17)
    (hmod : 1021 % 17 = 1) : SeventeenCertificate 1021 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 3
  let Q : ℤ[X] := X^15 - 2*X^14 + 7*X^13 - 20*X^12 + 61*X^11 - 182*X^10 + 547*X^9 - 1640*X^8 + 4921*X^7
    - 14762*X^6 + 44287*X^5 - 132860*X^4 + 398581*X^3 - 1195742*X^2 + 3587227*X - 10761680
  let A : ℤ[X] := 31621
  let G : ℤ[X] := X^15 + X^13 + X^12 + X^10 + X^8 + X^6 + X^5 + X^4 + X^3 + X^2
  let Qp : ℤ[X] := 658*X^15 + 726*X^14 + 522*X^13 + 113*X^12 + 319*X^11 + 722*X^10 + 534*X^9 + 77*X^8
    + 427*X^7 + 398*X^6 + 485*X^5 + 224*X^4 - 14*X^3 + 700*X^2 + 600*X - 121
  let Rp : ℤ[X] := -658*X^14 - 68*X^13 - 454*X^12 - 317*X^11 - 70*X^10 - 448*X^9 + 323*X^8 - 606*X^7
    - 224*X^6 + 14*X^5 - 700*X^4 - 600*X^3 + 121*X^2 - 1021*X + 1021
  let QP : ℤ[X] := 2*X^15 + 2*X^14 + X^13 + X^11 + 2*X^10 + X^9 + X^7 + X^6 + X^5 + 2*X^2 + X - 1
  let RP : ℤ[X] := -2*X^14 - X^12 - X^11 - X^9 + X^8 - 2*X^7 - 2*X^4 - X^3 - 2*X + 3
  let C1 : ℤ[X] := X^14 - 3*X^13 + 10*X^12 - 29*X^11 + 87*X^10 - 260*X^9 + 780*X^8 - 2339*X^7 + 7017*X^6
    - 21050*X^5 + 63151*X^4 - 189452*X^3 + 568357*X^2 - 1705070*X + 5115210
  let C2 : ℤ[X] := -15030
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
theorem seventeenCertificate_1123 [Fact (Nat.Prime 1123)]
    (hpn : 1123 ≠ 17)
    (hmod : 1123 % 17 = 1) : SeventeenCertificate 1123 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 85
  let Q : ℤ[X] := X^15 - 84*X^14 + 7141*X^13 - 606984*X^12 + 51593641*X^11 - 4385459484*X^10
    + 372764056141*X^9 - 31684944771984*X^8 + 2693220305618641*X^7 - 228923725977584484*X^6
    + 19458516708094681141*X^5 - 1653973920188047896984*X^4 + 140587783215984071243641*X^3
    - 11949961573358646055709484*X^2 + 1015746733735484914735306141*X - 86338472367516217752501021984
  let A : ℤ[X] := 6534968968155724406912365867
  let G : ℤ[X] := X^15 - 2*X^13 - X^12 + X^11 - X^9 - X^8 + X^7 - X^5 - X^4 + X^2 - X - 1
  let Qp : ℤ[X] := 346*X^15 + 134*X^14 + 186*X^13 + 258*X^12 - 247*X^11 + 4*X^10 + 6*X^9 - 164*X^8
    - 313*X^7 - X^6 - 692*X^5 - 353*X^4 + 30*X^3 + 42*X^2 + 145*X + 374
  let Rp : ℤ[X] := -346*X^14 + 212*X^13 + 640*X^12 - 150*X^11 + 51*X^10 + 157*X^9 - 646*X^8 + 229*X^7
    + 403*X^6 - 565*X^5 + 82*X^4 + 114*X^3 - 706*X^2 - 978*X + 1497
  let QP : ℤ[X] := 26*X^15 + 10*X^14 + 14*X^13 + 19*X^12 - 19*X^11 - 13*X^8 - 24*X^7 - X^6 - 53*X^5
    - 27*X^4 + 2*X^3 + 3*X^2 + 11*X + 28
  let RP : ℤ[X] := -26*X^14 + 16*X^13 + 48*X^12 - 11*X^11 + 4*X^10 + 11*X^9 - 49*X^8 + 18*X^7 + 30*X^6
    - 43*X^5 + 6*X^4 + 8*X^3 - 54*X^2 - 73*X + 113
  let C1 : ℤ[X] := X^14 - 85*X^13 + 7223*X^12 - 613956*X^11 + 52186261*X^10 - 4435832185*X^9
    + 377045735724*X^8 - 32048887536541*X^7 + 2724155440605986*X^6 - 231553212451508810*X^5
    + 19682023058378248849*X^4 - 1672971959962151152166*X^3 + 142202616596782847934110*X^2
    - 12087222410726542074399349*X + 1027413904911756076323944664
  let C2 : ℤ[X] := -77765077397595072562364467
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
theorem seventeenCertificate_1259 [Fact (Nat.Prime 1259)]
    (hpn : 1259 ≠ 17)
    (hmod : 1259 % 17 = 1) : SeventeenCertificate 1259 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 91
  let Q : ℤ[X] := X^15 - 90*X^14 + 8191*X^13 - 745380*X^12 + 67829581*X^11 - 6172491870*X^10
    + 561696760171*X^9 - 51114405175560*X^8 + 4651410870975961*X^7 - 423278389258812450*X^6
    + 38518333422551932951*X^5 - 3505168341452225898540*X^4 + 318970319072152556767141*X^3
    - 29026299035565882665809830*X^2 + 2641393212236495322588694531*X - 240366782313521074355571202320
  let A : ℤ[X] := 17373611747839887026494820819
  let G : ℤ[X] := X^11 + X^7 - X^3 + 1
  let Qp : ℤ[X] := 722*X^15 + 488*X^14 + 379*X^13 + 226*X^12 + 300*X^11 + 1120*X^10 + 781*X^9 + 155*X^8
    + 466*X^7 + 1122*X^6 + 599*X^5 + 350*X^4 + 347*X^3 + 620*X^2 + 957*X + 506
  let Rp : ℤ[X] := -722*X^10 + 234*X^9 + 109*X^8 + 153*X^7 - 796*X^6 - 586*X^5 + 448*X^4 + 779*X^3
    + 337*X^2 - 1710*X + 753
  let QP : ℤ[X] := 52*X^15 + 35*X^14 + 27*X^13 + 16*X^12 + 22*X^11 + 81*X^10 + 56*X^9 + 11*X^8 + 34*X^7
    + 81*X^6 + 43*X^5 + 25*X^4 + 25*X^3 + 45*X^2 + 69*X + 36
  let RP : ℤ[X] := -52*X^10 + 17*X^9 + 8*X^8 + 11*X^7 - 58*X^6 - 42*X^5 + 33*X^4 + 56*X^3 + 23*X^2 - 123*X + 55
  let C1 : ℤ[X] := X^10 - 91*X^9 + 8281*X^8 - 753571*X^7 + 68574962*X^6 - 6240321542*X^5
    + 567869260322*X^4 - 51676102689302*X^3 + 4702525344726481*X^2 - 427929806370109771*X
    + 38941612379679989161
  let C2 : ℤ[X] := -2814683658896647350
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
theorem seventeenCertificate_1327 [Fact (Nat.Prime 1327)]
    (hpn : 1327 ≠ 17)
    (hmod : 1327 % 17 = 1) : SeventeenCertificate 1327 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 75
  let Q : ℤ[X] := X^15 - 74*X^14 + 5551*X^13 - 416324*X^12 + 31224301*X^11 - 2341822574*X^10
    + 175636693051*X^9 - 13172751978824*X^8 + 987956398411801*X^7 - 74096729880885074*X^6
    + 5557254741066380551*X^5 - 416794105579978541324*X^4 + 31259557918498390599301*X^3
    - 2344466843887379294947574*X^2 + 175835013291553447121068051*X - 13187625996866508534080103824
  let A : ℤ[X] := 745344347976630098007541663
  let G : ℤ[X] := X^14 + X^13 + X^12 + X^11 + X^10 + X^9 + X^8 + X^7 + X^5 + X^4 + 2*X^3 + 2*X^2 + X + 1
  let Qp : ℤ[X] := -239*X^15 + 435*X^14 + 311*X^13 + 322*X^12 - 503*X^11 + 330*X^10 + 224*X^9 + 212*X^8
    - 215*X^7 - 38*X^6 - 43*X^5 + 332*X^4 + 74*X^3 - 481*X^2 + 7*X + 563
  let Rp : ℤ[X] := 239*X^13 - 435*X^12 - 311*X^11 - 322*X^10 + 503*X^9 - 330*X^8 - 224*X^7 - 212*X^6
    - 24*X^5 + 712*X^4 - 81*X^3 - 82*X^2 - 1334*X + 764
  let QP : ℤ[X] := -13*X^15 + 25*X^14 + 18*X^13 + 18*X^12 - 28*X^11 + 19*X^10 + 13*X^9 + 12*X^8 - 12*X^7
    - 2*X^6 - 2*X^5 + 19*X^4 + 4*X^3 - 27*X^2 + X + 32
  let RP : ℤ[X] := 13*X^13 - 25*X^12 - 18*X^11 - 18*X^10 + 28*X^9 - 19*X^8 - 13*X^7 - 12*X^6 - X^5
    + 40*X^4 - 5*X^3 - 6*X^2 - 75*X + 43
  let C1 : ℤ[X] := X^13 - 74*X^12 + 5551*X^11 - 416324*X^10 + 31224301*X^9 - 2341822574*X^8
    + 175636693051*X^7 - 13172751978824*X^6 + 987956398411800*X^5 - 74096729880884999*X^4
    + 5557254741066374926*X^3 - 416794105579978119448*X^2 + 31259557918498358958602*X
    - 2344466843887376921895149
  let C2 : ℤ[X] := 132505661862511883302288
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
theorem seventeenCertificate_1361 [Fact (Nat.Prime 1361)]
    (hpn : 1361 ≠ 17)
    (hmod : 1361 % 17 = 1) : SeventeenCertificate 1361 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 137
  let Q : ℤ[X] := X^15 - 136*X^14 + 18633*X^13 - 2552720*X^12 + 349722641*X^11 - 47912001816*X^10
    + 6563944248793*X^9 - 899260362084640*X^8 + 123198669605595681*X^7 - 16878217735966608296*X^6
    + 2312315829827425336553*X^5 - 316787268686357271107760*X^4 + 43399855810030946141763121*X^3
    - 5945780245974239621421547576*X^2 + 814571893698470828134752017913*X
    - 111596349436690503454461026454080
  let A : ℤ[X] := 11233431207073180729802469231601
  let G : ℤ[X] := -X^13 - X^12 - X^6 - X^3 - X^2 - X - 1
  let Qp : ℤ[X] := 388*X^15 + 311*X^14 - 28*X^13 + 141*X^12 + 125*X^11 + 956*X^10 + 72*X^9 + 51*X^8
    + 206*X^7 + 747*X^6 + 124*X^5 - 268*X^4 + 357*X^3 + 475*X^2 + 641*X - 325
  let Rp : ℤ[X] := 388*X^12 + 311*X^11 - 416*X^10 - 170*X^9 + 153*X^8 + 815*X^7 - 53*X^6 - 517*X^5
    + 57*X^4 + 357*X^3 + 475*X^2 - 720*X + 1036
  let QP : ℤ[X] := 39*X^15 + 31*X^14 - 3*X^13 + 14*X^12 + 13*X^11 + 96*X^10 + 7*X^9 + 5*X^8 + 21*X^7
    + 75*X^6 + 12*X^5 - 27*X^4 + 36*X^3 + 48*X^2 + 64*X - 33
  let RP : ℤ[X] := 39*X^12 + 31*X^11 - 42*X^10 - 17*X^9 + 16*X^8 + 82*X^7 - 6*X^6 - 52*X^5 + 6*X^4
    + 36*X^3 + 47*X^2 - 72*X + 104
  let C1 : ℤ[X] := -X^12 + 136*X^11 - 18632*X^10 + 2552584*X^9 - 349704008*X^8 + 47909449096*X^7
    - 6563594526152*X^6 + 899212450082823*X^5 - 123192105661346751*X^4 + 16877318475604504887*X^3
    - 2312192631157817169520*X^2 + 316770390468620952224239*X - 43397543494201070454720744
  let C2 : ℤ[X] := 4368452210658006357308407
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
theorem seventeenCertificate_1429 [Fact (Nat.Prime 1429)]
    (hpn : 1429 ≠ 17)
    (hmod : 1429 % 17 = 1) : SeventeenCertificate 1429 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 135
  let Q : ℤ[X] := X^15 - 134*X^14 + 18091*X^13 - 2442284*X^12 + 329708341*X^11 - 44510626034*X^10
    + 6008934514591*X^9 - 811206159469784*X^8 + 109512831528420841*X^7 - 14784232256336813534*X^6
    + 1995871354605469827091*X^5 - 269442632871738426657284*X^4 + 36374755437684687598733341*X^3
    - 4910591984087432825829001034*X^2 + 662929917851803431486915139591*X
    - 89495538909993463250733543844784
  let A : ℤ[X] := 8454791989397563008291832343629
  let G : ℤ[X] := -X^11 + X^6 + X^4 + X^2
  let Qp : ℤ[X] := 279*X^15 - 232*X^14 + 161*X^13 - 21*X^12 + 256*X^11 + 15*X^10 - 317*X^9 + 204*X^8
    - 110*X^7 - 590*X^6 - 95*X^5 + 243*X^4 + 341*X^3 - 28*X^2 - 228*X - 379
  let Rp : ℤ[X] := 279*X^10 - 511*X^9 + 393*X^8 - 182*X^7 + 277*X^6 - 520*X^5 + 179*X^4 - 151*X^3
    + 379*X^2 - 1429*X + 1429
  let QP : ℤ[X] := 26*X^15 - 22*X^14 + 15*X^13 - 2*X^12 + 24*X^11 + X^10 - 30*X^9 + 19*X^8 - 11*X^7
    - 56*X^6 - 9*X^5 + 23*X^4 + 32*X^3 - 3*X^2 - 22*X - 36
  let RP : ℤ[X] := 26*X^10 - 48*X^9 + 37*X^8 - 17*X^7 + 26*X^6 - 49*X^5 + 17*X^4 - 14*X^3 + 35*X^2
    - 134*X + 135
  let C1 : ℤ[X] := -X^10 + 135*X^9 - 18225*X^8 + 2460375*X^7 - 332150625*X^6 + 44840334376*X^5
    - 6053445140760*X^4 + 817215094002601*X^3 - 110324037690351135*X^2 + 14893745088197403226*X
    - 2010655586906649435510
  let C2 : ℤ[X] := 189949967972286685650
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
theorem seventeenCertificate_1531 [Fact (Nat.Prime 1531)]
    (hpn : 1531 ≠ 17)
    (hmod : 1531 % 17 = 1) : SeventeenCertificate 1531 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 34
  let Q : ℤ[X] := X^15 - 33*X^14 + 1123*X^13 - 38181*X^12 + 1298155*X^11 - 44137269*X^10
    + 1500667147*X^9 - 51022682997*X^8 + 1734771221899*X^7 - 58982221544565*X^6 + 2005395532515211*X^5
    - 68183448105517173*X^4 + 2318237235587583883*X^3 - 78820066009977852021*X^2
    + 2679882244339246968715*X - 91115996307534396936309
  let A : ℤ[X] := 2023477383707491506097
  let G : ℤ[X] := X^7 + X^6 + X^4 + X + 1
  let Qp : ℤ[X] := -346*X^15 - 830*X^14 + 316*X^13 - 373*X^12 + 88*X^11 - 276*X^10 - 148*X^9 + 93*X^8
    - 446*X^7 - 492*X^6 - 459*X^5 - 50*X^4 - 177*X^3 - 452*X^2 - 288*X + 260
  let Rp : ℤ[X] := 346*X^6 + 830*X^5 - 662*X^4 - 111*X^3 + 712*X^2 - 1243*X + 1271
  let QP : ℤ[X] := -8*X^15 - 18*X^14 + 7*X^13 - 8*X^12 + 2*X^11 - 6*X^10 - 3*X^9 + 2*X^8 - 10*X^7
    - 11*X^6 - 10*X^5 - X^4 - 4*X^3 - 10*X^2 - 6*X + 6
  let RP : ℤ[X] := 8*X^6 + 18*X^5 - 15*X^4 - 2*X^3 + 15*X^2 - 27*X + 28
  let C1 : ℤ[X] := X^6 - 33*X^5 + 1122*X^4 - 38147*X^3 + 1296998*X^2 - 44097932*X + 1499329689
  let C2 : ℤ[X] := -33296675
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
