import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 4421 through 5849. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_4421 [Fact (Nat.Prime 4421)]
    (hpn : 4421 ≠ 17)
    (hmod : 4421 % 17 = 1) : SeventeenCertificate 4421 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 291
  let Q : ℤ[X] := X^15 - 290*X^14 + 84391*X^13 - 24557780*X^12 + 7146313981*X^11 - 2079577368470*X^10
    + 605157014224771*X^9 - 176100691139408360*X^8 + 51245301121567832761*X^7
    - 14912382626376239333450*X^6 + 4339503344275485646033951*X^5 - 1262795473184166322995879740*X^4
    + 367473482696592399991801004341*X^3 - 106934783464708388397614092263230*X^2
    + 31118021988230141023705700848599931*X - 9055344398574971037898358946942579920
  let A : ℤ[X] := 596042800268110511655377166604906301
  let G : ℤ[X] := X^7 + X^5 + X^2 + X + 1
  let Qp : ℤ[X] := -647*X^15 - 2473*X^14 - 1627*X^13 - 237*X^12 - 2416*X^11 - 530*X^10 - 1152*X^9
    - 1411*X^8 - 1199*X^7 - 997*X^6 - 2306*X^5 - 1593*X^4 - 1289*X^3 - 1333*X^2 - 1792*X - 853
  let Rp : ℤ[X] := 647*X^6 + 1826*X^5 - 199*X^4 + 436*X^3 + 1333*X^2 - 2629*X + 5274
  let QP : ℤ[X] := -43*X^15 - 163*X^14 - 107*X^13 - 16*X^12 - 159*X^11 - 35*X^10 - 76*X^9 - 93*X^8
    - 79*X^7 - 66*X^6 - 152*X^5 - 105*X^4 - 85*X^3 - 88*X^2 - 118*X - 56
  let RP : ℤ[X] := 43*X^6 + 120*X^5 - 13*X^4 + 29*X^3 + 87*X^2 - 172*X + 347
  let C1 : ℤ[X] := X^6 - 291*X^5 + 84682*X^4 - 24642462*X^3 + 7170956442*X^2 - 2086748324621*X
    + 607243762464712
  let C2 : ℤ[X] := -39970127771371
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
theorem seventeenCertificate_4523 [Fact (Nat.Prime 4523)]
    (hpn : 4523 ≠ 17)
    (hmod : 4523 % 17 = 1) : SeventeenCertificate 4523 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 164
  let Q : ℤ[X] := X^15 - 163*X^14 + 26733*X^13 - 4384211*X^12 + 719010605*X^11 - 117917739219*X^10
    + 19338509231917*X^9 - 3171515514034387*X^8 + 520128544301639469*X^7 - 85301081265468872915*X^6
    + 13989377327536895158061*X^5 - 2294257881716050805922003*X^4 + 376258292601432332171208493*X^3
    - 61706359986634902476078192851*X^2 + 10119843037808124006076823627565*X
    - 1659654258200532336996599074920659
  let A : ℤ[X] := 60177602994668870941287253656199
  let G : ℤ[X] := X^14 + X^12 + X^11 + X^9 + X^7 + X^6 + X^3 + X
  let Qp : ℤ[X] := -447*X^15 + 493*X^14 + 115*X^13 - 1215*X^12 - 199*X^11 + 528*X^10 - 1102*X^9
    - 639*X^8 + 320*X^7 + 1349*X^6 - 56*X^5 - 309*X^4 + 476*X^3 - 1620*X^2 - 1624*X - 968
  let Rp : ℤ[X] := 447*X^13 - 940*X^12 + 825*X^11 + 837*X^10 - 1578*X^9 + 1428*X^8 + 1004*X^7 - 1381*X^6
    + 781*X^5 - 1440*X^4 + 964*X^3 + 656*X^2 - 3555*X + 4523
  let QP : ℤ[X] := -16*X^15 + 18*X^14 + 4*X^13 - 44*X^12 - 7*X^11 + 19*X^10 - 40*X^9 - 23*X^8 + 12*X^7
    + 49*X^6 - 2*X^5 - 11*X^4 + 17*X^3 - 59*X^2 - 59*X - 35
  let RP : ℤ[X] := 16*X^13 - 34*X^12 + 30*X^11 + 30*X^10 - 57*X^9 + 52*X^8 + 36*X^7 - 50*X^6 + 28*X^5
    - 52*X^4 + 35*X^3 + 23*X^2 - 128*X + 164
  let C1 : ℤ[X] := X^13 - 164*X^12 + 26897*X^11 - 4411107*X^10 + 723421548*X^9 - 118641133871*X^8
    + 19457145954844*X^7 - 3190971936594415*X^6 + 523319397601484061*X^5 - 85824381206643386004*X^4
    + 14075198517889515304656*X^3 - 2308332556933880509963583*X^2 + 378566539337156403634027612*X
    - 62084912451293650195980528367
  let C2 : ℤ[X] := 2251144294055308121189654356
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
theorem seventeenCertificate_4591 [Fact (Nat.Prime 4591)]
    (hpn : 4591 ≠ 17)
    (hmod : 4591 % 17 = 1) : SeventeenCertificate 4591 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 842
  let Q : ℤ[X] := X^15 - 841*X^14 + 708123*X^13 - 596239565*X^12 + 502033713731*X^11
    - 422712386961501*X^10 + 355923829821583843*X^9 - 299687864709773595805*X^8
    + 252337182085629367667811*X^7 - 212467907316099927576296861*X^6
    + 178897977960156139019241956963*X^5 - 150632097442451469054201727762845*X^4
    + 126832226046544136943637854776315491*X^3 - 106792734331190163306543073721657643421*X^2
    + 89919482306862117504109268073635735760483*X - 75712204102377902938460003718001289510326685
  let A : ℤ[X] := 13885793041647178016594058621336764488715981
  let G : ℤ[X] := X^15 + X^14 + X^11 + X^10 + X^7 + 2*X^6 + X^5 + X^2 + X - 1
  let Qp : ℤ[X] := -2104*X^15 - 2662*X^14 - 1108*X^13 - 1141*X^12 - 901*X^11 - 977*X^10 - 1259*X^9
    - 2547*X^8 - 1527*X^7 - 1850*X^6 - 753*X^5 - 1636*X^4 - 1892*X^3 - 2117*X^2 - 898*X - 3503
  let Rp : ℤ[X] := 2104*X^14 + 2662*X^13 - 996*X^12 - 1521*X^11 + 1897*X^10 + 2498*X^9 - 638*X^8
    + 49*X^7 + 2165*X^6 + 3905*X^5 + 1250*X^4 - 1161*X^3 - 321*X^2 + 1517*X + 1088
  let QP : ℤ[X] := -386*X^15 - 488*X^14 - 203*X^13 - 209*X^12 - 165*X^11 - 179*X^10 - 231*X^9 - 467*X^8
    - 280*X^7 - 339*X^6 - 138*X^5 - 300*X^4 - 347*X^3 - 388*X^2 - 165*X - 642
  let RP : ℤ[X] := 386*X^14 + 488*X^13 - 183*X^12 - 279*X^11 + 348*X^10 + 458*X^9 - 117*X^8 + 9*X^7
    + 397*X^6 + 716*X^5 + 229*X^4 - 213*X^3 - 59*X^2 + 278*X + 200
  let C1 : ℤ[X] := X^14 - 841*X^13 + 708122*X^12 - 596238724*X^11 + 502033005609*X^10
    - 422711790722777*X^9 + 355923327788578234*X^8 - 299687441997982873028*X^7
    + 252336826162301579089577*X^6 - 212467607628657929593423832*X^5
    + 178897725623329976717662866545*X^4 - 150631884974843840396272133630890*X^3
    + 126832047148818513613661136517209380*X^2 - 106792583699305188462702676947490297959*X
    + 89919355474814968685595653989786830881479
  let C2 : ℤ[X] := -16491417405749118630640718941276521804009
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
theorem seventeenCertificate_4931 [Fact (Nat.Prime 4931)]
    (hpn : 4931 ≠ 17)
    (hmod : 4931 % 17 = 1) : SeventeenCertificate 4931 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 1211
  let Q : ℤ[X] := X^15 - 1210*X^14 + 1465311*X^13 - 1774491620*X^12 + 2148909351821*X^11
    - 2602329225055230*X^10 + 3151420691541883531*X^9 - 3816370457457220956040*X^8
    + 4621624623980694577764441*X^7 - 5596787419640621133672738050*X^6
    + 6777709565184792192877685778551*X^5 - 8207806283438783345574877477825260*X^4
    + 9939653409244366631491176625646389861*X^3 - 12036920278594927990735814893657778121670*X^2
    + 14576710457378457796781071836219569305342371*X - 17652396363885312391901877993661898428769611280
  let A : ℤ[X] := 4335236665314360840923377458999099370764550651
  let G : ℤ[X] := X^10 + X^9 + X^8 + X^5 + X^4 + X^2 + X + 1
  let Qp : ℤ[X] := 1781*X^15 - 163*X^14 + 1934*X^13 + 1932*X^12 - 577*X^11 + 326*X^10 + 1475*X^9
    + 578*X^8 + 2025*X^7 + 213*X^6 + 250*X^5 - 178*X^4 + 375*X^3 + 1308*X^2 + 644*X + 995
  let Rp : ℤ[X] := -1781*X^9 + 163*X^8 - 1934*X^7 - 151*X^6 + 414*X^5 - 173*X^4 + 620*X^3 - 1308*X^2
    - 5575*X + 3936
  let QP : ℤ[X] := 437*X^15 - 40*X^14 + 475*X^13 + 474*X^12 - 142*X^11 + 80*X^10 + 362*X^9 + 142*X^8
    + 497*X^7 + 52*X^6 + 61*X^5 - 44*X^4 + 92*X^3 + 321*X^2 + 158*X + 244
  let RP : ℤ[X] := -437*X^9 + 40*X^8 - 475*X^7 - 37*X^6 + 102*X^5 - 42*X^4 + 152*X^3 - 322*X^2 - 1368*X + 967
  let C1 : ℤ[X] := X^9 - 1210*X^8 + 1465311*X^7 - 1774491621*X^6 + 2148909353031*X^5
    - 2602329226520540*X^4 + 3151420693316373941*X^3 - 3816370459606128842551*X^2
    + 4621624626583022028329262*X - 5596787422792039676306736281
  let C2 : ℤ[X] := 1374510153924388571893623532
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
theorem seventeenCertificate_4999 [Fact (Nat.Prime 4999)]
    (hpn : 4999 ≠ 17)
    (hmod : 4999 % 17 = 1) : SeventeenCertificate 4999 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 26
  let Q : ℤ[X] := X^15 - 25*X^14 + 651*X^13 - 16925*X^12 + 440051*X^11 - 11441325*X^10 + 297474451*X^9
    - 7734335725*X^8 + 201092728851*X^7 - 5228410950125*X^6 + 135938684703251*X^5 - 3534405802284525*X^4
    + 91894550859397651*X^3 - 2389258322344338925*X^2 + 62120716380952812051*X - 1615138625904773113325
  let A : ℤ[X] := 8400400934891798549
  let G : ℤ[X] := X^10 - X^9 + X^4 + X^2 + 1
  let Qp : ℤ[X] := 2165*X^15 + 864*X^14 - 303*X^13 + 45*X^12 + 995*X^11 + 1290*X^10 - 1381*X^9
    - 1921*X^8 + 2121*X^7 + 2008*X^6 - 53*X^5 - 1456*X^4 + 29*X^3 + 1411*X^2 + 472*X - 109
  let Rp : ℤ[X] := -2165*X^9 + 3466*X^8 - 134*X^7 - 1515*X^6 - 602*X^5 + 655*X^4 + 801*X^3 - 830*X^2
    - 5580*X + 5108
  let QP : ℤ[X] := 11*X^15 + 4*X^14 - 2*X^13 + 5*X^11 + 6*X^10 - 8*X^9 - 10*X^8 + 11*X^7 + 10*X^6 - X^5
    - 8*X^4 + 7*X^2 + 2*X - 1
  let RP : ℤ[X] := -11*X^9 + 18*X^8 - X^7 - 8*X^6 - 3*X^5 + 4*X^4 + 4*X^3 - 5*X^2 - 28*X + 27
  let C1 : ℤ[X] := X^9 - 27*X^8 + 702*X^7 - 18252*X^6 + 474552*X^5 - 12338352*X^4 + 320797153*X^3
    - 8340725978*X^2 + 216858875429*X - 5638330761154
  let C2 : ℤ[X] := 29325184995
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
theorem seventeenCertificate_5101 [Fact (Nat.Prime 5101)]
    (hpn : 5101 ≠ 17)
    (hmod : 5101 % 17 = 1) : SeventeenCertificate 5101 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 198
  let Q : ℤ[X] := X^15 - 197*X^14 + 39007*X^13 - 7723385*X^12 + 1529230231*X^11 - 302787585737*X^10
    + 59951941975927*X^9 - 11870484511233545*X^8 + 2350355933224241911*X^7 - 465370474778399898377*X^6
    + 92143354006123179878647*X^5 - 18244384093212389615972105*X^4 + 3612388050456053143962476791*X^3
    - 715252833990298522504570404617*X^2 + 141620061130079107455904940114167*X
    - 28040772103755663276269178142605065
  let A : ℤ[X] := 1088428323180478598059458394870771
  let G : ℤ[X] := X^8 - X^7 - X^6 - X^4 - 1
  let Qp : ℤ[X] := -2459*X^15 - 172*X^14 + 991*X^13 + 262*X^12 - 3325*X^11 - 2138*X^10 + 2583*X^9
    + 1308*X^8 - 1292*X^7 - 1693*X^6 + 1190*X^5 + 1668*X^4 - 1158*X^3 - 2720*X^2 + 496*X + 1353
  let Rp : ℤ[X] := 2459*X^7 - 4746*X^6 - 1335*X^5 + 4179*X^4 + 1562*X^3 - 3216*X^2 - 5958*X + 6454
  let QP : ℤ[X] := -95*X^15 - 6*X^14 + 39*X^13 + 10*X^12 - 129*X^11 - 82*X^10 + 101*X^9 + 51*X^8
    - 50*X^7 - 65*X^6 + 47*X^5 + 65*X^4 - 45*X^3 - 105*X^2 + 20*X + 53
  let RP : ℤ[X] := 95*X^7 - 184*X^6 - 51*X^5 + 163*X^4 + 60*X^3 - 126*X^2 - 230*X + 251
  let C1 : ℤ[X] := X^7 - 199*X^6 + 39401*X^5 - 7801398*X^4 + 1544676803*X^3 - 305846006994*X^2
    + 60557509384812*X - 11990386858192776
  let C2 : ℤ[X] := 465417878439947
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
theorem seventeenCertificate_5237 [Fact (Nat.Prime 5237)]
    (hpn : 5237 ≠ 17)
    (hmod : 5237 % 17 = 1) : SeventeenCertificate 5237 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 135
  let Q : ℤ[X] := X^15 - 134*X^14 + 18091*X^13 - 2442284*X^12 + 329708341*X^11 - 44510626034*X^10
    + 6008934514591*X^9 - 811206159469784*X^8 + 109512831528420841*X^7 - 14784232256336813534*X^6
    + 1995871354605469827091*X^5 - 269442632871738426657284*X^4 + 36374755437684687598733341*X^3
    - 4910591984087432825829001034*X^2 + 662929917851803431486915139591*X
    - 89495538909993463250733543844784
  let A : ℤ[X] := 2307026494720091185573616272493
  let G : ℤ[X] := X^14 + X^9 + X^7 + X^5 + X^2 + X + 1
  let Qp : ℤ[X] := -344*X^15 - 1037*X^14 - 1748*X^13 - 29*X^12 - 1666*X^11 - 625*X^10 + 239*X^9
    - 1187*X^8 - 2446*X^7 - 65*X^6 - 2043*X^5 - 2100*X^4 + 358*X^3 - 1541*X^2 - 1789*X + 269
  let Rp : ℤ[X] := 344*X^13 + 693*X^12 + 711*X^11 - 1719*X^10 + 1637*X^9 - 697*X^8 - 171*X^7 + 2481*X^6
    + 233*X^5 + 311*X^4 - 89*X^3 + 1541*X^2 - 3448*X + 4968
  let QP : ℤ[X] := -9*X^15 - 27*X^14 - 45*X^13 - X^12 - 43*X^11 - 16*X^10 + 6*X^9 - 31*X^8 - 63*X^7
    - 2*X^6 - 53*X^5 - 54*X^4 + 9*X^3 - 40*X^2 - 46*X + 7
  let RP : ℤ[X] := 9*X^13 + 18*X^12 + 18*X^11 - 44*X^10 + 42*X^9 - 18*X^8 - 4*X^7 + 64*X^6 + 6*X^5
    + 8*X^4 - 2*X^3 + 39*X^2 - 88*X + 128
  let C1 : ℤ[X] := X^13 - 135*X^12 + 18225*X^11 - 2460375*X^10 + 332150625*X^9 - 44840334374*X^8
    + 6053445140490*X^7 - 817215093966149*X^6 + 110324037685430115*X^5 - 14893745087533065524*X^4
    + 2010655586816963845740*X^3 - 271438504220290119174900*X^2 + 36644198069739166088611501*X
    - 4946966739414787421962552634
  let C2 : ℤ[X] := 127523488604352931442609243
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
theorem seventeenCertificate_5407 [Fact (Nat.Prime 5407)]
    (hpn : 5407 ≠ 17)
    (hmod : 5407 % 17 = 1) : SeventeenCertificate 5407 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 732
  let Q : ℤ[X] := X^15 - 731*X^14 + 535093*X^13 - 391688075*X^12 + 286715670901*X^11
    - 209875871099531*X^10 + 153629137644856693*X^9 - 112456528756035099275*X^8
    + 82318179049417692669301*X^7 - 60256907064173751033928331*X^6 + 44108055970975185756835538293*X^5
    - 32287096970753835974003614030475*X^4 + 23634154982591807932970645470307701*X^3
    - 17300201447257203406934512484265237131*X^2 + 12663747459392272893876063138482153579893*X
    - 9269863140275143758317278217368936420481675
  let A : ℤ[X] := 1254954654832884266892592501408185955204843
  let G : ℤ[X] := X^9 - X^8 + X^3 + 1
  let Qp : ℤ[X] := -274*X^15 + 235*X^14 + 730*X^13 + 659*X^12 - 1439*X^11 - 1291*X^10 - 1487*X^9
    + 1403*X^8 + 60*X^7 - 938*X^6 - 347*X^5 - 399*X^4 - 184*X^3 - 761*X^2 - 143*X + 1669
  let Rp : ℤ[X] := 274*X^8 - 783*X^7 + 14*X^6 + 566*X^5 + 2027*X^4 - 2246*X^3 + 618*X^2 - 3595*X + 3738
  let QP : ℤ[X] := -37*X^15 + 32*X^14 + 99*X^13 + 89*X^12 - 195*X^11 - 175*X^10 - 201*X^9 + 190*X^8
    + 8*X^7 - 127*X^6 - 47*X^5 - 54*X^4 - 25*X^3 - 103*X^2 - 19*X + 226
  let RP : ℤ[X] := 37*X^8 - 106*X^7 + 2*X^6 + 77*X^5 + 274*X^4 - 304*X^3 + 83*X^2 - 486*X + 506
  let C1 : ℤ[X] := X^8 - 733*X^7 + 536556*X^6 - 392758992*X^5 + 287499582144*X^4 - 210449694129408*X^3
    + 154049176102726657*X^2 - 112763996907195912924*X + 82543245736067408260368
  let C2 : ℤ[X] := -11174709798187783030625
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
theorem seventeenCertificate_5441 [Fact (Nat.Prime 5441)]
    (hpn : 5441 ≠ 17)
    (hmod : 5441 % 17 = 1) : SeventeenCertificate 5441 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 244
  let Q : ℤ[X] := X^15 - 243*X^14 + 59293*X^13 - 14467491*X^12 + 3530067805*X^11 - 861336544419*X^10
    + 210166116838237*X^9 - 51280532508529827*X^8 + 12512449932081277789*X^7
    - 3053037783427831780515*X^6 + 744941219156390954445661*X^5 - 181765657474159392884741283*X^4
    + 44350820423694891863876873053*X^3 - 10821600183381553614785957024931*X^2
    + 2640470444745099082007773514083165*X - 644274788517804176009896737436292259
  let A : ℤ[X] := 28892308104823418295610145917010717
  let G : ℤ[X] := X^15 + X^12 + X^10 + X^4 + X - 1
  let Qp : ℤ[X] := -896*X^15 + 88*X^14 - 604*X^13 - 427*X^12 - 87*X^11 - 1432*X^10 + 288*X^9 - 435*X^8
    + 1865*X^7 + 1088*X^6 + 241*X^5 + 151*X^4 + 347*X^3 + 1492*X^2 - 397*X - 1966
  let Rp : ℤ[X] := 896*X^14 - 984*X^13 + 692*X^12 + 719*X^11 - 1324*X^10 + 2933*X^9 - 2881*X^8
    + 1075*X^7 - 1132*X^6 - 1283*X^5 + 2915*X^4 - 3034*X^3 + 320*X^2 - 1906*X + 3475
  let QP : ℤ[X] := -40*X^15 + 4*X^14 - 27*X^13 - 19*X^12 - 4*X^11 - 64*X^10 + 13*X^9 - 19*X^8 + 84*X^7
    + 49*X^6 + 11*X^5 + 7*X^4 + 16*X^3 + 67*X^2 - 18*X - 88
  let RP : ℤ[X] := 40*X^14 - 44*X^13 + 31*X^12 + 32*X^11 - 59*X^10 + 131*X^9 - 129*X^8 + 48*X^7 - 51*X^6
    - 57*X^5 + 130*X^4 - 136*X^3 + 14*X^2 - 85*X + 156
  let C1 : ℤ[X] := X^14 - 244*X^13 + 59536*X^12 - 14526783*X^11 + 3544535052*X^10 - 864866552687*X^9
    + 211027438855628*X^8 - 51490695080773232*X^7 + 12563729599708668608*X^6
    - 3065550022328915140352*X^5 + 747994205448255294245888*X^4 - 182510586129374291795996671*X^3
    + 44532583015567327198223187724*X^2 - 10865950255798427836366457804656*X
    + 2651291862414816392073415704336065
  let C2 : ℤ[X] := -118896381993974489922057237981621
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
theorem seventeenCertificate_5849 [Fact (Nat.Prime 5849)]
    (hpn : 5849 ≠ 17)
    (hmod : 5849 % 17 = 1) : SeventeenCertificate 5849 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 70
  let Q : ℤ[X] := X^15 - 69*X^14 + 4831*X^13 - 338169*X^12 + 23671831*X^11 - 1657028169*X^10
    + 115991971831*X^9 - 8119438028169*X^8 + 568360661971831*X^7 - 39785246338028169*X^6
    + 2784967243661971831*X^5 - 194947707056338028169*X^4 + 13646339493943661971831*X^3
    - 955243764576056338028169*X^2 + 66867063520323943661971831*X - 4680694446422676056338028169
  let A : ℤ[X] := 56017885322206757384794319
  let G : ℤ[X] := -X^14 - X^12 - X^11 - X^9 - X^3 - X^2
  let Qp : ℤ[X] := -1254*X^15 - 1209*X^14 + 1490*X^13 - 272*X^12 + 239*X^11 - 437*X^10 + 91*X^9
    - 1775*X^8 + 167*X^7 - 1246*X^6 - 1769*X^5 - 253*X^4 - 1091*X^3 - 921*X^2 - 1123*X + 1319
  let Rp : ℤ[X] := -1254*X^13 + 45*X^12 + 1445*X^11 - 2971*X^10 + 3255*X^9 - 993*X^8 - 678*X^7 + 668*X^6
    + 32*X^5 - 2240*X^4 - 1123*X^3 + 1319*X^2 - 5849*X + 5849
  let QP : ℤ[X] := -15*X^15 - 14*X^14 + 18*X^13 - 3*X^12 + 3*X^11 - 5*X^10 + X^9 - 21*X^8 + 2*X^7
    - 15*X^6 - 21*X^5 - 3*X^4 - 13*X^3 - 11*X^2 - 13*X + 16
  let RP : ℤ[X] := -15*X^13 + X^12 + 17*X^11 - 35*X^10 + 39*X^9 - 12*X^8 - 8*X^7 + 8*X^6 - 27*X^4
    - 13*X^3 + 15*X^2 - 69*X + 70
  let C1 : ℤ[X] := -X^13 + 70*X^12 - 4901*X^11 + 343069*X^10 - 24014830*X^9 + 1681038099*X^8
    - 117672666930*X^7 + 8237086685100*X^6 - 576596067957000*X^5 + 40361724756990000*X^4
    - 2825320732989300000*X^3 + 197772451309250999999*X^2 - 13844071591647569999931*X
    + 969085011415329899995170
  let C2 : ℤ[X] := -11597871567630892973100
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
