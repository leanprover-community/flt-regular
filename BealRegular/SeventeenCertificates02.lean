import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 1667 through 2857. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_1667 [Fact (Nat.Prime 1667)]
    (hpn : 1667 ≠ 17)
    (hmod : 1667 % 17 = 1) : SeventeenCertificate 1667 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 263
  let Q : ℤ[X] := X^15 - 262*X^14 + 68907*X^13 - 18122540*X^12 + 4766228021*X^11 - 1253517969522*X^10
    + 329675225984287*X^9 - 86704584433867480*X^8 + 22803305706107147241*X^7
    - 5997269400706179724382*X^6 + 1577281852385725267512467*X^5 - 414825127177445745355778820*X^4
    + 109099008447668231028569829661*X^3 - 28693039221736744760513865200842*X^2
    + 7546269315316763872015146547821447*X - 1984668829928308898339983542077040560
  let A : ℤ[X] := 313118117739139316294790444850786843
  let G : ℤ[X] := -X^11 - X^8 - X^7 - X^6 - X^5 - 1
  let Qp : ℤ[X] := -188*X^15 - 754*X^14 - 259*X^13 - 418*X^12 - 276*X^11 - 948*X^10 - 914*X^9 + 146*X^8
    - 245*X^7 - 766*X^6 - 437*X^5 - 280*X^4 + 104*X^3 - 868*X^2 - 283*X - 774
  let Rp : ℤ[X] := -188*X^10 - 566*X^9 + 495*X^8 - 347*X^7 - 612*X^6 - 931*X^5 - 384*X^4 + 972*X^3
    - 585*X^2 - 1176*X + 893
  let QP : ℤ[X] := -30*X^15 - 119*X^14 - 41*X^13 - 66*X^12 - 44*X^11 - 150*X^10 - 144*X^9 + 23*X^8
    - 39*X^7 - 121*X^6 - 69*X^5 - 44*X^4 + 16*X^3 - 137*X^2 - 45*X - 122
  let RP : ℤ[X] := -30*X^10 - 89*X^9 + 78*X^8 - 55*X^7 - 97*X^6 - 147*X^5 - 60*X^4 + 153*X^3 - 93*X^2
    - 185*X + 141
  let C1 : ℤ[X] := -X^10 + 263*X^9 - 69169*X^8 + 18191446*X^7 - 4784350299*X^6 + 1258284128636*X^5
    - 330928725831269*X^4 + 87034254893623747*X^3 - 22890009037023045461*X^2 + 6020072376737060956243*X
    - 1583279035081847031491909
  let C2 : ℤ[X] := 249791473441227216126198
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
theorem seventeenCertificate_1871 [Fact (Nat.Prime 1871)]
    (hpn : 1871 ≠ 17)
    (hmod : 1871 % 17 = 1) : SeventeenCertificate 1871 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 598
  let Q : ℤ[X] := X^15 - 597*X^14 + 357007*X^13 - 213490185*X^12 + 127667130631*X^11
    - 76344944117337*X^10 + 45654276582167527*X^9 - 27301257396136181145*X^8
    + 16326151922889436324711*X^7 - 9763038849887882922177177*X^6 + 5838297232232953987461951847*X^5
    - 3491301744875306484502247204505*X^4 + 2087798443435433277732343828293991*X^3
    - 1248503469174389100083941609319806617*X^2 + 746605074566284681850197082373244356967*X
    - 446469834590638239746417855259200125466265
  let A : ℤ[X] := 142698536122502227348133552883485662762601
  let G : ℤ[X] := X^8 - X^3 - X - 1
  let Qp : ℤ[X] := 811*X^15 + 422*X^14 + 1040*X^13 + 63*X^12 + 557*X^11 + 763*X^10 + 1061*X^9 + 602*X^8
    + 47*X^7 + 770*X^6 + 617*X^5 + 432*X^4 + 673*X^3 + 622*X^2 + 1184*X + 17
  let Rp : ℤ[X] := -811*X^7 + 389*X^6 - 618*X^5 + 977*X^4 - 494*X^3 + 605*X^2 - 687*X + 1888
  let QP : ℤ[X] := 259*X^15 + 135*X^14 + 332*X^13 + 20*X^12 + 178*X^11 + 244*X^10 + 339*X^9 + 192*X^8
    + 15*X^7 + 246*X^6 + 197*X^5 + 138*X^4 + 215*X^3 + 199*X^2 + 378*X + 5
  let RP : ℤ[X] := -259*X^7 + 124*X^6 - 197*X^5 + 312*X^4 - 158*X^3 + 193*X^2 - 219*X + 603
  let C1 : ℤ[X] := X^7 - 598*X^6 + 357604*X^5 - 213847192*X^4 + 127880620816*X^3 - 76472611247969*X^2
    + 45730621526285462*X - 27346911672718706277
  let C2 : ℤ[X] := 8740488070703252995
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
theorem seventeenCertificate_1973 [Fact (Nat.Prime 1973)]
    (hpn : 1973 ≠ 17)
    (hmod : 1973 % 17 = 1) : SeventeenCertificate 1973 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 25
  let Q : ℤ[X] := X^15 - 24*X^14 + 601*X^13 - 15024*X^12 + 375601*X^11 - 9390024*X^10 + 234750601*X^9
    - 5868765024*X^8 + 146719125601*X^7 - 3667978140024*X^6 + 91699453500601*X^5 - 2292486337515024*X^4
    + 57312158437875601*X^3 - 1432803960946890024*X^2 + 35820099023672250601*X - 895502475591806265024
  let A : ℤ[X] := 11346964972019846237
  let G : ℤ[X] := -X^15 - X^12 - X^10 - X^9 - X^3 - X
  let Qp : ℤ[X] := -5*X^15 + 120*X^14 + 941*X^13 + 146*X^12 + 291*X^11 + 612*X^10 + 479*X^9 - 142*X^8
    - 401*X^7 + 155*X^6 + 66*X^5 + 318*X^4 - 63*X^3 - 403*X^2 + 205*X + 789
  let Rp : ℤ[X] := -5*X^14 + 125*X^13 + 821*X^12 - 800*X^11 + 270*X^10 + 1137*X^9 - 808*X^8 + 470*X^7
    + 88*X^6 - 227*X^5 - 244*X^4 + 181*X^3 - 584*X^2 - 1184*X + 1973
  let QP : ℤ[X] := 2*X^14 + 12*X^13 + 2*X^12 + 4*X^11 + 8*X^10 + 6*X^9 - 2*X^8 - 5*X^7 + 2*X^6 + X^5
    + 4*X^4 - X^3 - 5*X^2 + 3*X + 10
  let RP : ℤ[X] := 2*X^13 + 10*X^12 - 10*X^11 + 4*X^10 + 14*X^9 - 10*X^8 + 6*X^7 + X^6 - 3*X^5 - 3*X^4
    + 2*X^3 - 8*X^2 - 14*X + 25
  let C1 : ℤ[X] := -X^14 + 25*X^13 - 625*X^12 + 15624*X^11 - 390600*X^10 + 9764999*X^9 - 244124976*X^8
    + 6103124400*X^7 - 152578110000*X^6 + 3814452750000*X^5 - 95361318750000*X^4 + 2384032968750000*X^3
    - 59600824218750001*X^2 + 1490020605468750025*X - 37250515136718750626
  let C2 : ℤ[X] := 472003486273679050
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
theorem seventeenCertificate_2143 [Fact (Nat.Prime 2143)]
    (hpn : 2143 ≠ 17)
    (hmod : 2143 % 17 = 1) : SeventeenCertificate 2143 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 175
  let Q : ℤ[X] := X^15 - 174*X^14 + 30451*X^13 - 5328924*X^12 + 932561701*X^11 - 163198297674*X^10
    + 28559702092951*X^9 - 4997947866266424*X^8 + 874640876596624201*X^7 - 153062153404409235174*X^6
    + 26785876845771616155451*X^5 - 4687528448010032827203924*X^4 + 820317478401755744760686701*X^3
    - 143555558720307255333120172674*X^2 + 25122222776053769683296030217951*X
    - 4396388985809409694576805288141424
  let A : ℤ[X] := 359014499541132382898245882139407
  let G : ℤ[X] := -X^14 - X^8 - X^7 - X^5 + X
  let Qp : ℤ[X] := 448*X^15 - 804*X^14 - 290*X^13 - 234*X^12 + 681*X^11 - 862*X^10 - 855*X^9 + 63*X^8
    + 138*X^7 - 129*X^6 - 550*X^5 + 263*X^4 - 574*X^3 + 177*X^2 - 525*X + 174
  let Rp : ℤ[X] := 448*X^13 - 1252*X^12 + 514*X^11 + 56*X^10 + 915*X^9 - 1543*X^8 + 455*X^7 + 114*X^6
    - 663*X^5 + 751*X^4 - 702*X^3 + 699*X^2 - 2317*X + 2143
  let QP : ℤ[X] := 36*X^15 - 66*X^14 - 24*X^13 - 19*X^12 + 55*X^11 - 71*X^10 - 70*X^9 + 5*X^8 + 11*X^7
    - 11*X^6 - 45*X^5 + 21*X^4 - 47*X^3 + 14*X^2 - 43*X + 14
  let RP : ℤ[X] := 36*X^13 - 102*X^12 + 42*X^11 + 5*X^10 + 74*X^9 - 126*X^8 + 37*X^7 + 9*X^6 - 54*X^5
    + 61*X^4 - 57*X^3 + 56*X^2 - 188*X + 175
  let C1 : ℤ[X] := -X^13 + 175*X^12 - 30625*X^11 + 5359375*X^10 - 937890625*X^9 + 164130859375*X^8
    - 28722900390626*X^7 + 5026507568359549*X^6 - 879638824462921075*X^5 + 153936794281011188124*X^4
    - 26938938999176957921700*X^3 + 4714314324855967636297500*X^2 - 825005006849794336352062500*X
    + 144375876198714008861610937501
  let C2 : ℤ[X] := -11789910562190831334942563725
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
theorem seventeenCertificate_2347 [Fact (Nat.Prime 2347)]
    (hpn : 2347 ≠ 17)
    (hmod : 2347 % 17 = 1) : SeventeenCertificate 2347 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 28
  let Q : ℤ[X] := X^15 - 27*X^14 + 757*X^13 - 21195*X^12 + 593461*X^11 - 16616907*X^10 + 465273397*X^9
    - 13027655115*X^8 + 364774343221*X^7 - 10213681610187*X^6 + 285983085085237*X^5
    - 8007526382386635*X^4 + 224210738706825781*X^3 - 6277900683791121867*X^2 + 175781219146151412277*X
    - 4921874136092239543755
  let A : ℤ[X] := 58718566600163062303
  let G : ℤ[X] := -X^15 - X^14 - X^10 - X^6 - X^5 - 1
  let Qp : ℤ[X] := 93*X^15 - 164*X^14 - 9*X^13 + 345*X^12 - 179*X^11 + 411*X^10 + 320*X^9 + 521*X^8
    - 413*X^7 - 78*X^6 - 70*X^5 - 294*X^4 - 1063*X^3 - 654*X^2 - 371*X - 1254
  let Rp : ℤ[X] := 93*X^14 - 164*X^13 - 102*X^12 + 509*X^11 - 170*X^10 + 159*X^9 + 242*X^8 + 265*X^7
    - 379*X^6 - 1030*X^5 + 769*X^4 - 409*X^3 - 283*X^2 - 1464*X + 1093
  let QP : ℤ[X] := X^15 - 2*X^14 + 4*X^12 - 2*X^11 + 5*X^10 + 4*X^9 + 6*X^8 - 5*X^7 - X^6 - X^5 - 4*X^4
    - 13*X^3 - 8*X^2 - 5*X - 15
  let RP : ℤ[X] := X^14 - 2*X^13 - X^12 + 6*X^11 - 2*X^10 + 2*X^9 + 3*X^8 + 3*X^7 - 5*X^6 - 12*X^5
    + 9*X^4 - 5*X^3 - 4*X^2 - 17*X + 13
  let C1 : ℤ[X] := -X^14 + 27*X^13 - 756*X^12 + 21168*X^11 - 592704*X^10 + 16595711*X^9 - 464679908*X^8
    + 13011037424*X^7 - 364309047872*X^6 + 10200653340415*X^5 - 285618293531621*X^4
    + 7997312218885388*X^3 - 223924742128790864*X^2 + 6269892779606144192*X - 175556997828972037376
  let C2 : ℤ[X] := 2094416676272354941
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
theorem seventeenCertificate_2381 [Fact (Nat.Prime 2381)]
    (hpn : 2381 ≠ 17)
    (hmod : 2381 % 17 = 1) : SeventeenCertificate 2381 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 486
  let Q : ℤ[X] := X^15 - 485*X^14 + 235711*X^13 - 114555545*X^12 + 55673994871*X^11
    - 27057561507305*X^10 + 13149974892550231*X^9 - 6390887797779412265*X^8 + 3105971469720794360791*X^7
    - 1509502134284306059344425*X^6 + 733618037262172744841390551*X^5
    - 356538366109415953992915807785*X^4 + 173277645929176153640557082583511*X^3
    - 84212935921579610669310742135586345*X^2 + 40927486857887690785285020677894963671*X
    - 19890758612933417721648520049456952344105
  let A : ℤ[X] := 4060020447663015965023595440586341385651
  let G : ℤ[X] := -X^15 - X^14 - X^9 - X^8 - X^7 - X^3 - X^2 - X - 1
  let Qp : ℤ[X] := -123*X^15 + 130*X^14 + 984*X^13 + 234*X^12 + 441*X^11 - 159*X^10 + 959*X^9 + 479*X^8
    + 421*X^7 + 37*X^6 + 943*X^5 + 1112*X^4 - 68*X^3 - 409*X^2 + 1028*X + 279
  let Rp : ℤ[X] := -123*X^14 + 130*X^13 + 1107*X^12 + 104*X^11 - 543*X^10 - 393*X^9 + 395*X^8 + 768*X^7
    + 446*X^6 - 85*X^5 + 833*X^4 - 68*X^3 - 409*X^2 - 1353*X + 2660
  let QP : ℤ[X] := -25*X^15 + 27*X^14 + 201*X^13 + 48*X^12 + 90*X^11 - 32*X^10 + 196*X^9 + 98*X^8
    + 86*X^7 + 8*X^6 + 193*X^5 + 227*X^4 - 14*X^3 - 83*X^2 + 210*X + 57
  let RP : ℤ[X] := -25*X^14 + 27*X^13 + 226*X^12 + 21*X^11 - 111*X^10 - 80*X^9 + 81*X^8 + 157*X^7
    + 91*X^6 - 17*X^5 + 170*X^4 - 14*X^3 - 84*X^2 - 275*X + 543
  let C1 : ℤ[X] := -X^14 + 485*X^13 - 235710*X^12 + 114555060*X^11 - 55673759160*X^10
    + 27057446951760*X^9 - 13149919218555361*X^8 + 6390860740217905445*X^7 - 3105958319745902046271*X^6
    + 1509495743396508394487706*X^5 - 733614931290703079721025116*X^4
    + 356536856607281696744418206376*X^3 - 173276912311138904617787248298737*X^2
    + 84212579383213507644244602673186181*X - 40927313580241764715102876899168483967
  let C2 : ℤ[X] := 8353916169675555502536748497688317181
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
theorem seventeenCertificate_2551 [Fact (Nat.Prime 2551)]
    (hpn : 2551 ≠ 17)
    (hmod : 2551 % 17 = 1) : SeventeenCertificate 2551 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 12
  let Q : ℤ[X] := X^15 - 11*X^14 + 133*X^13 - 1595*X^12 + 19141*X^11 - 229691*X^10 + 2756293*X^9
    - 33075515*X^8 + 396906181*X^7 - 4762874171*X^6 + 57154490053*X^5 - 685853880635*X^4
    + 8230246567621*X^3 - 98762958811451*X^2 + 1185155505737413*X - 14221866068848955
  let A : ℤ[X] := 66900193189411
  let G : ℤ[X] := X^10 + X^9 + X^4 + 1
  let Qp : ℤ[X] := 219*X^15 + 142*X^14 + 1066*X^13 + 182*X^12 + 586*X^11 + 840*X^10 + 343*X^9 + 1205*X^8
    + 1065*X^7 + 194*X^6 + 442*X^5 + 17*X^4 + 15*X^3 + 39*X^2 - 249*X + 656
  let Rp : ℤ[X] := -219*X^9 - 142*X^8 - 847*X^7 - 40*X^6 + 480*X^5 - 658*X^4 + 24*X^3 - 288*X^2 - 1646*X + 1895
  let QP : ℤ[X] := X^15 + X^14 + 5*X^13 + X^12 + 3*X^11 + 4*X^10 + 2*X^9 + 6*X^8 + 5*X^7 + X^6 + 2*X^5 - X + 3
  let RP : ℤ[X] := -X^9 - X^8 - 4*X^7 + 2*X^5 - 3*X^4 - 2*X^2 - 7*X + 9
  let C1 : ℤ[X] := X^9 - 11*X^8 + 132*X^7 - 1584*X^6 + 19008*X^5 - 228096*X^4 + 2737153*X^3
    - 32845836*X^2 + 394150032*X - 4729800384
  let C2 : ℤ[X] := 22249159
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
theorem seventeenCertificate_2687 [Fact (Nat.Prime 2687)]
    (hpn : 2687 ≠ 17)
    (hmod : 2687 % 17 = 1) : SeventeenCertificate 2687 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 271
  let Q : ℤ[X] := X^15 - 270*X^14 + 73171*X^13 - 19829340*X^12 + 5373751141*X^11 - 1456286559210*X^10
    + 394653657545911*X^9 - 106951141194941880*X^8 + 28983759263829249481*X^7
    - 7854598760497726609350*X^6 + 2128596264094883911133851*X^5 - 576849587569713539917273620*X^4
    + 156326238231392369317581151021*X^3 - 42364410560707332085064491926690*X^2
    + 11480755261951686995052477312132991*X - 3111284675988907175659221351588040560
  let A : ℤ[X] := 313791643912539577448324892549445103
  let G : ℤ[X] := -X^14 - X^12 - X^11 - X^6 - X^3 + X^2 - X - 1
  let Qp : ℤ[X] := 1683*X^15 - 307*X^14 - 1104*X^13 - 77*X^12 + 1054*X^11 + 871*X^10 - 589*X^9 + 82*X^8
    + 957*X^7 + 288*X^6 - 1129*X^5 - 1363*X^4 + 250*X^3 + 1108*X^2 - 328*X - 787
  let Rp : ℤ[X] := 1683*X^13 - 1990*X^12 + 886*X^11 + 720*X^10 - 1656*X^9 + 47*X^8 + 698*X^7 + 1619*X^6
    + 915*X^5 - 3448*X^4 - 668*X^3 + 2682*X^2 - 3015*X + 1900
  let QP : ℤ[X] := 169*X^15 - 32*X^14 - 112*X^13 - 8*X^12 + 106*X^11 + 87*X^10 - 60*X^9 + 8*X^8 + 96*X^7
    + 28*X^6 - 115*X^5 - 138*X^4 + 25*X^3 + 111*X^2 - 34*X - 80
  let RP : ℤ[X] := 169*X^13 - 201*X^12 + 89*X^11 + 72*X^10 - 167*X^9 + 5*X^8 + 71*X^7 + 163*X^6 + 91*X^5
    - 348*X^4 - 67*X^3 + 270*X^2 - 304*X + 191
  let C1 : ℤ[X] := -X^13 + 271*X^12 - 73442*X^11 + 19902781*X^10 - 5393653651*X^9 + 1461680139421*X^8
    - 396115317783091*X^7 + 107347251119217661*X^6 - 29091105053307986132*X^5
    + 7883689469446464241772*X^4 - 2136479846219991809520212*X^3 + 578986038325617780379977451*X^2
    - 156905216386242418482973889220*X + 42521313640671695408885923978619
  let C2 : ℤ[X] := -4288528469155946950430995682250
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
theorem seventeenCertificate_2789 [Fact (Nat.Prime 2789)]
    (hpn : 2789 ≠ 17)
    (hmod : 2789 % 17 = 1) : SeventeenCertificate 2789 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 74
  let Q : ℤ[X] := X^15 - 73*X^14 + 5403*X^13 - 399821*X^12 + 29586755*X^11 - 2189419869*X^10
    + 162017070307*X^9 - 11989263202717*X^8 + 887205477001059*X^7 - 65653205298078365*X^6
    + 4858337192057799011*X^5 - 359516952212277126813*X^4 + 26604254463708507384163*X^3
    - 1968714830314429546428061*X^2 + 145684897443267786435676515*X - 10780682410801816196240062109
  let A : ℤ[X] := 286041770670252563112859303
  let G : ℤ[X] := -X^12 - X^11 - X^10 - X^9 - X^4 - X
  let Qp : ℤ[X] := 1624*X^15 + 1375*X^14 + 278*X^13 + 575*X^12 + 909*X^11 + 1294*X^10 + 694*X^9
    + 470*X^8 + 312*X^7 + 848*X^6 + 230*X^5 + 1338*X^4 + 227*X^3 + 1560*X^2 + 533*X + 1228
  let Rp : ℤ[X] := 1624*X^11 + 1375*X^10 + 278*X^9 + 575*X^8 - 715*X^7 - 81*X^6 + 416*X^5 - 105*X^4
    + 1027*X^3 - 695*X^2 - 1561*X + 2789
  let QP : ℤ[X] := 43*X^15 + 36*X^14 + 7*X^13 + 15*X^12 + 24*X^11 + 34*X^10 + 18*X^9 + 12*X^8 + 8*X^7
    + 22*X^6 + 6*X^5 + 35*X^4 + 6*X^3 + 41*X^2 + 14*X + 32
  let RP : ℤ[X] := 43*X^11 + 36*X^10 + 7*X^9 + 15*X^8 - 19*X^7 - 2*X^6 + 11*X^5 - 3*X^4 + 27*X^3
    - 19*X^2 - 41*X + 74
  let C1 : ℤ[X] := -X^11 + 73*X^10 - 5403*X^9 + 399821*X^8 - 29586754*X^7 + 2189419796*X^6
    - 162017064904*X^5 + 11989262802896*X^4 - 887205447414305*X^3 + 65653203108658570*X^2
    - 4858337030040734180*X + 359516940223014329319
  let C2 : ℤ[X] := -9538993752779871054
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
theorem seventeenCertificate_2857 [Fact (Nat.Prime 2857)]
    (hpn : 2857 ≠ 17)
    (hmod : 2857 % 17 = 1) : SeventeenCertificate 2857 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 8
  let Q : ℤ[X] := X^15 - 7*X^14 + 57*X^13 - 455*X^12 + 3641*X^11 - 29127*X^10 + 233017*X^9 - 1864135*X^8
    + 14913081*X^7 - 119304647*X^6 + 954437177*X^5 - 7635497415*X^4 + 61083979321*X^3 - 488671834567*X^2
    + 3909374676537*X - 31274997412295
  let A : ℤ[X] := 87574371473
  let G : ℤ[X] := -X^15 + X^13 - X^11 - X^10 + X^9 - X^6 - X^2 + 1
  let Qp : ℤ[X] := -11*X^15 + 77*X^14 - 627*X^13 - 709*X^12 - 53*X^11 + 413*X^10 - 458*X^9 + 796*X^8
    - 665*X^7 - 405*X^6 + 372*X^5 - 130*X^4 + 1029*X^3 + 328*X^2 + 222*X + 1070
  let Rp : ℤ[X] := -11*X^14 + 88*X^13 - 693*X^12 - 170*X^11 + 1349*X^10 + 625*X^9 - 2132*X^8 - 86*X^7
    + 688*X^6 + 199*X^5 + 1265*X^4 - 1549*X^3 + 964*X^2 - 2009*X + 1787
  let QP : ℤ[X] := -2*X^13 - 2*X^12 + X^10 - X^9 + 2*X^8 - 2*X^7 - X^6 + X^5 + 3*X^3 + X^2 + X + 3
  let RP : ℤ[X] := -2*X^12 + 4*X^10 + X^9 - 6*X^8 + 2*X^6 + X^5 + 3*X^4 - 4*X^3 + 2*X^2 - 5*X + 5
  let C1 : ℤ[X] := -X^14 + 8*X^13 - 63*X^12 + 504*X^11 - 4033*X^10 + 32263*X^9 - 258103*X^8
    + 2064824*X^7 - 16518592*X^6 + 132148735*X^5 - 1057189880*X^4 + 8457519040*X^3 - 67660152320*X^2
    + 541281218559*X - 4330249748472
  let C2 : ℤ[X] := 12125305561
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
