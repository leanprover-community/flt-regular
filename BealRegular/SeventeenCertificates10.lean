import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 12547 through 13159. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_12547 [Fact (Nat.Prime 12547)]
    (hpn : 12547 ≠ 17)
    (hmod : 12547 % 17 = 1) : SeventeenCertificate 12547 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 851
  let Q : ℤ[X] := X^15 - 850*X^14 + 723351*X^13 - 615571700*X^12 + 523851516701*X^11
    - 445797640712550*X^10 + 379373792246380051*X^9 - 322847097201669423400*X^8
    + 274742879718620679313401*X^7 - 233806190640546198095704250*X^6
    + 198969068235104814579444316751*X^5 - 169322677068074197207107113555100*X^4
    + 144093598184931141823248153635390101*X^3 - 122623652055376401691584178743716975950*X^2
    + 104352727899125317839538136110903146533451*X - 88804171442155645481446953830378577699966800
  let A : ℤ[X] := 6023140981690798940361150690177107645068283
  let G : ℤ[X] := X^10 + X^9 + X^7 + X^6 + X^4 + X + 1
  let Qp : ℤ[X] := 1717*X^15 - 3998*X^14 + 3778*X^13 - 1329*X^12 + 3466*X^11 + 696*X^10 - 870*X^9
    + 1814*X^8 + 1284*X^7 + 622*X^6 - 631*X^5 - 823*X^4 - 542*X^3 - 1280*X^2 - 592*X + 3629
  let Rp : ℤ[X] := -1717*X^9 + 3998*X^8 - 2061*X^7 - 4386*X^6 + 4310*X^5 - 4086*X^4 - 50*X^3 + 4909*X^2
    - 11955*X + 8918
  let QP : ℤ[X] := 116*X^15 - 271*X^14 + 256*X^13 - 90*X^12 + 235*X^11 + 47*X^10 - 59*X^9 + 123*X^8
    + 87*X^7 + 42*X^6 - 43*X^5 - 56*X^4 - 37*X^3 - 87*X^2 - 40*X + 246
  let RP : ℤ[X] := -116*X^9 + 271*X^8 - 140*X^7 - 297*X^6 + 292*X^5 - 277*X^4 - 3*X^3 + 332*X^2 - 810*X + 605
  let C1 : ℤ[X] := X^9 - 850*X^8 + 723350*X^7 - 615570849*X^6 + 523850792500*X^5 - 445797024417500*X^4
    + 379373267779292501*X^3 - 322846650880177918351*X^2 + 274742499899031408516701*X
    - 233805867414075728647712550
  let C2 : ℤ[X] := 15857877832898576956978033
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
theorem seventeenCertificate_12853 [Fact (Nat.Prime 12853)]
    (hpn : 12853 ≠ 17)
    (hmod : 12853 % 17 = 1) : SeventeenCertificate 12853 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 476
  let Q : ℤ[X] := X^15 - 475*X^14 + 226101*X^13 - 107624075*X^12 + 51229059701*X^11
    - 24385032417675*X^10 + 11607275430813301*X^9 - 5525063105067131275*X^8 + 2629930038011954486901*X^7
    - 1251846698093690335764875*X^6 + 595879028292596599824080501*X^5
    - 283638417467275981516262318475*X^4 + 135011886714423367201740863594101*X^3
    - 64265658076065522788028651070792075*X^2 + 30590453244207188847101637909697027701*X
    - 14561055744242621891220379645015785185675
  let A : ℤ[X] := 539256401949699526975873392284098167617
  let G : ℤ[X] := X^15 + 2*X^14 + X^13 + X^11 + 2*X^10 + X^6 - X^4 + X^2 + X
  let Qp : ℤ[X] := 1026*X^15 + 1064*X^14 - 4171*X^13 - 5793*X^12 - 4901*X^11 - 5344*X^10 - 124*X^9
    - 4215*X^8 + 2298*X^7 - 317*X^6 - 2318*X^5 - 964*X^4 - 2818*X^3 - 7171*X^2 - 4476*X - 1996
  let Rp : ℤ[X] := -1026*X^14 - 2090*X^13 + 4133*X^12 + 12054*X^11 + 6561*X^10 - 1809*X^9 - 67*X^8
    + 6186*X^7 - 1199*X^6 - 8687*X^5 - 3654*X^4 + 5175*X^3 + 4476*X^2 - 10857*X + 12853
  let QP : ℤ[X] := 38*X^15 + 39*X^14 - 155*X^13 - 215*X^12 - 182*X^11 - 198*X^10 - 5*X^9 - 156*X^8
    + 85*X^7 - 12*X^6 - 86*X^5 - 36*X^4 - 105*X^3 - 266*X^2 - 166*X - 74
  let RP : ℤ[X] := -38*X^14 - 77*X^13 + 154*X^12 + 447*X^11 + 243*X^10 - 67*X^9 - 2*X^8 + 229*X^7
    - 45*X^6 - 322*X^5 - 135*X^4 + 192*X^3 + 165*X^2 - 401*X + 476
  let C1 : ℤ[X] := X^14 - 474*X^13 + 225625*X^12 - 107397500*X^11 + 51121210001*X^10
    - 24333695960474*X^9 + 11582839277185624*X^8 - 5513431495940357024*X^7 + 2624393392067609943424*X^6
    - 1249211254624182333069823*X^5 + 594624557201110790541235748*X^4
    - 283041289227728736297628216049*X^3 + 134727653672398878477671030839324*X^2
    - 64130363148061866155371410679518223*X + 30526052858477448289956791483450674149
  let C2 : ℤ[X] := -1130506586838501936203176903923015708
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
theorem seventeenCertificate_13159 [Fact (Nat.Prime 13159)]
    (hpn : 13159 ≠ 17)
    (hmod : 13159 % 17 = 1) : SeventeenCertificate 13159 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 255
  let Q : ℤ[X] := X^15 - 254*X^14 + 64771*X^13 - 16516604*X^12 + 4211734021*X^11 - 1073992175354*X^10
    + 273868004715271*X^9 - 69836341202394104*X^8 + 17808267006610496521*X^7
    - 4541108086685676612854*X^6 + 1157982562104847536277771*X^5 - 295285553336736121750831604*X^4
    + 75297816100867711046462059021*X^3 - 19200943105721266316847825050354*X^2
    + 4896240491958922910796195387840271*X - 1248541325449525342253029823899269104
  let A : ℤ[X] := 24194698532535068187135998563288519
  let G : ℤ[X] := X^15 + X^14 + X^11 + X^10 + 2*X^7 + X^6 + X^3 + X^2 - 1
  let Qp : ℤ[X] := 1603*X^15 + 767*X^14 + 3403*X^13 + 2332*X^12 - 902*X^11 + 7910*X^10 - 2120*X^9
    + 2684*X^8 + 1451*X^7 + 50*X^6 + 2012*X^5 + 1744*X^4 + 4289*X^3 + 105*X^2 + 1146*X - 1129
  let Rp : ℤ[X] := -1603*X^14 - 767*X^13 - 1800*X^12 - 1565*X^11 + 2702*X^10 - 6345*X^9 - 582*X^8
    + 3661*X^7 - 2472*X^6 - 2875*X^5 - 3779*X^4 + 3038*X^3 + 88*X^2 - 10884*X + 12030
  let QP : ℤ[X] := 31*X^15 + 15*X^14 + 66*X^13 + 45*X^12 - 17*X^11 + 153*X^10 - 41*X^9 + 52*X^8 + 28*X^7
    + X^6 + 39*X^5 + 34*X^4 + 83*X^3 + 2*X^2 + 22*X - 22
  let RP : ℤ[X] := -31*X^14 - 15*X^13 - 35*X^12 - 30*X^11 + 52*X^10 - 123*X^9 - 11*X^8 + 71*X^7 - 48*X^6
    - 56*X^5 - 73*X^4 + 59*X^3 + X^2 - 210*X + 233
  let C1 : ℤ[X] := X^14 - 254*X^13 + 64770*X^12 - 16516350*X^11 + 4211669251*X^10 - 1073975659004*X^9
    + 273863793046020*X^8 - 69835267226735100*X^7 + 17807993142817450502*X^6
    - 4541038251418449878009*X^5 + 1157964754111704718892295*X^4 - 295281012298484703317535225*X^3
    + 75296658136113599345971482376*X^2 - 19200647824708967833222728005879*X
    + 4896165195300786797471795641499145
  let C2 : ℤ[X] := -94879711589155759051243095112264
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
