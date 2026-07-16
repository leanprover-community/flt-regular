import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 3061 through 4217. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_3061 [Fact (Nat.Prime 3061)]
    (hpn : 3061 ≠ 17)
    (hmod : 3061 % 17 = 1) : SeventeenCertificate 3061 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 5
  let Q : ℤ[X] := X^15 - 4*X^14 + 21*X^13 - 104*X^12 + 521*X^11 - 2604*X^10 + 13021*X^9 - 65104*X^8
    + 325521*X^7 - 1627604*X^6 + 8138021*X^5 - 40690104*X^4 + 203450521*X^3 - 1017252604*X^2
    + 5086263021*X - 25431315104
  let A : ℤ[X] := 41540861
  let G : ℤ[X] := -X^15 - X^13 - X^12 - X^9 - X^7 - X^6 - X^5 - X^3
  let Qp : ℤ[X] := -1030*X^15 - 2002*X^14 - 203*X^13 - 15*X^12 - 955*X^11 - 2377*X^10 - 1389*X^9
    - 207*X^8 + 5*X^7 - 1055*X^6 - 1877*X^5 - 828*X^4 + 49*X^3 - 1275*X^2 - 777*X - 206
  let Rp : ℤ[X] := -1030*X^14 - 972*X^13 + 769*X^12 - 1814*X^11 - 113*X^10 + 565*X^9 - 794*X^8
    - 2152*X^7 + 547*X^6 - 704*X^5 - 571*X^4 - 206*X^3 - 3061*X + 3061
  let QP : ℤ[X] := -2*X^15 - 3*X^14 - 2*X^11 - 4*X^10 - 2*X^9 - 2*X^6 - 3*X^5 - X^4 - 2*X^2 - X
  let RP : ℤ[X] := -2*X^14 - X^13 + X^12 - 3*X^11 + X^9 - 2*X^8 - 3*X^7 + X^6 - X^5 - X^4 - X^2 - 4*X + 5
  let C1 : ℤ[X] := -X^14 + 5*X^13 - 26*X^12 + 129*X^11 - 645*X^10 + 3225*X^9 - 16126*X^8 + 80630*X^7
    - 403151*X^6 + 2015754*X^5 - 10078771*X^4 + 50393855*X^3 - 251969276*X^2 + 1259846380*X - 6299231900
  let C2 : ℤ[X] := 10289500
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
theorem seventeenCertificate_3163 [Fact (Nat.Prime 3163)]
    (hpn : 3163 ≠ 17)
    (hmod : 3163 % 17 = 1) : SeventeenCertificate 3163 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 116
  let Q : ℤ[X] := X^15 - 115*X^14 + 13341*X^13 - 1547555*X^12 + 179516381*X^11 - 20823900195*X^10
    + 2415572422621*X^9 - 280206401024035*X^8 + 32503942518788061*X^7 - 3770457332179415075*X^6
    + 437373050532812148701*X^5 - 50735273861806209249315*X^4 + 5885291767969520272920541*X^3
    - 682693845084464351658782755*X^2 + 79192486029797864792418799581*X
    - 9186328379456552315920580751395
  let A : ℤ[X] := 336899807782788513641096227367
  let G : ℤ[X] := X^10 + X^9 + X^6 + X^5 + X^4 + X^2 + X
  let Qp : ℤ[X] := 612*X^15 - 794*X^14 + 989*X^13 - 244*X^12 + 449*X^11 - 864*X^10 - 380*X^9 + 410*X^8
    + 497*X^7 - 106*X^6 + 256*X^5 - 617*X^4 - 565*X^3 - 271*X^2 + 418*X - 431
  let Rp : ℤ[X] := -612*X^9 + 794*X^8 - 377*X^7 - 550*X^6 - 72*X^5 + 1414*X^4 - 160*X^3 - 418*X^2
    - 2732*X + 3163
  let QP : ℤ[X] := 22*X^15 - 29*X^14 + 36*X^13 - 9*X^12 + 16*X^11 - 32*X^10 - 14*X^9 + 15*X^8 + 18*X^7
    - 4*X^6 + 9*X^5 - 23*X^4 - 21*X^3 - 10*X^2 + 15*X - 16
  let RP : ℤ[X] := -22*X^9 + 29*X^8 - 14*X^7 - 20*X^6 - 2*X^5 + 52*X^4 - 6*X^3 - 16*X^2 - 99*X + 116
  let C1 : ℤ[X] := X^9 - 115*X^8 + 13340*X^7 - 1547440*X^6 + 179503041*X^5 - 20822352755*X^4
    + 2415392919581*X^3 - 280185578671396*X^2 + 32501527125881937*X - 3770177146602304691
  let C2 : ℤ[X] := 138267641165307412
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
theorem seventeenCertificate_3299 [Fact (Nat.Prime 3299)]
    (hpn : 3299 ≠ 17)
    (hmod : 3299 % 17 = 1) : SeventeenCertificate 3299 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 26
  let Q : ℤ[X] := X^15 - 25*X^14 + 651*X^13 - 16925*X^12 + 440051*X^11 - 11441325*X^10 + 297474451*X^9
    - 7734335725*X^8 + 201092728851*X^7 - 5228410950125*X^6 + 135938684703251*X^5 - 3534405802284525*X^4
    + 91894550859397651*X^3 - 2389258322344338925*X^2 + 62120716380952812051*X - 1615138625904773113325
  let A : ℤ[X] := 12729191959237375249
  let G : ℤ[X] := X^15 + X^12 + X^11 + X^8 + X^3 + X
  let Qp : ℤ[X] := -1047*X^15 - 217*X^14 - 2003*X^13 - 1753*X^12 - 1655*X^11 - 904*X^10 - 636*X^9
    - 1006*X^8 - 1283*X^7 - 679*X^6 + 112*X^5 - 660*X^4 - 382*X^3 - 1012*X^2 - 1127*X - 1436
  let Rp : ℤ[X] := 1047*X^14 - 830*X^13 + 1786*X^12 + 797*X^11 + 119*X^10 + 205*X^9 + 1268*X^8
    + 1069*X^7 - 1402*X^6 + 163*X^5 - 939*X^4 + 1321*X^3 - 309*X^2 - 1863*X + 3299
  let QP : ℤ[X] := -8*X^15 - 2*X^14 - 16*X^13 - 14*X^12 - 13*X^11 - 7*X^10 - 5*X^9 - 8*X^8 - 10*X^7
    - 5*X^6 + X^5 - 5*X^4 - 3*X^3 - 8*X^2 - 9*X - 11
  let RP : ℤ[X] := 8*X^14 - 6*X^13 + 14*X^12 + 6*X^11 + X^10 + 2*X^9 + 10*X^8 + 8*X^7 - 11*X^6 + X^5
    - 7*X^4 + 10*X^3 - 3*X^2 - 14*X + 26
  let C1 : ℤ[X] := X^14 - 26*X^13 + 676*X^12 - 17575*X^11 + 456951*X^10 - 11880726*X^9 + 308898876*X^8
    - 8031370775*X^7 + 208815640150*X^6 - 5429206643900*X^5 + 141159372741400*X^4 - 3670143691276400*X^3
    + 95423735973186401*X^2 - 2481017135302846426*X + 64506445517874007077
  let C2 : ℤ[X] := -508386657612829398
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
theorem seventeenCertificate_3469 [Fact (Nat.Prime 3469)]
    (hpn : 3469 ≠ 17)
    (hmod : 3469 % 17 = 1) : SeventeenCertificate 3469 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 394
  let Q : ℤ[X] := X^15 - 393*X^14 + 154843*X^13 - 61008141*X^12 + 24037207555*X^11 - 9470659776669*X^10
    + 3731439952007587*X^9 - 1470187341090989277*X^8 + 579253812389849775139*X^7
    - 228226002081600811404765*X^6 + 89921044820150719693477411*X^5 - 35428891659139383559230099933*X^4
    + 13958983313700917122336659373603*X^3 - 5499839425598161346200643793199581*X^2
    + 2166936733685675570403053654520634915*X - 853773073072156174738803139881130156509
  let A : ℤ[X] := 96969325681876486839748756734841534063
  let G : ℤ[X] := -2*X^15 - 2*X^14 - 2*X^11 - 2*X^10 - X^7 - 2*X^6 - X^5 + X^4 - X^3 - 2*X^2 - X + 1
  let Qp : ℤ[X] := 310*X^15 - 415*X^14 + 777*X^13 - 556*X^12 + 827*X^11 + 558*X^10 - 995*X^9 + 343*X^8
    + 459*X^7 - 148*X^6 - 351*X^5 - 156*X^4 - 668*X^3 - 142*X^2 + 754*X + 1568
  let Rp : ℤ[X] := 620*X^14 - 830*X^13 + 934*X^12 - 282*X^11 + 720*X^10 + 1398*X^9 - 2710*X^8 - 712*X^7
    + 3318*X^6 + 1141*X^5 - 5212*X^4 - 430*X^3 + 3218*X^2 - 1087*X + 1901
  let QP : ℤ[X] := 35*X^15 - 47*X^14 + 88*X^13 - 63*X^12 + 94*X^11 + 63*X^10 - 113*X^9 + 39*X^8 + 52*X^7
    - 17*X^6 - 40*X^5 - 18*X^4 - 76*X^3 - 16*X^2 + 86*X + 178
  let RP : ℤ[X] := 70*X^14 - 94*X^13 + 106*X^12 - 32*X^11 + 82*X^10 + 158*X^9 - 308*X^8 - 80*X^7
    + 377*X^6 + 128*X^5 - 592*X^4 - 48*X^3 + 365*X^2 - 123*X + 216
  let C1 : ℤ[X] := -2*X^14 + 786*X^13 - 309684*X^12 + 122015496*X^11 - 48074105426*X^10
    + 18941197537842*X^9 - 7462831829909748*X^8 + 2940355740984440712*X^7 - 1158500161947869640529*X^6
    + 456449063807460638368424*X^5 - 179840931140139491517159057*X^4 + 70857326869214959657760668459*X^3
    - 27917786786470694105157703372847*X^2 + 10999607993869453477432135128901716*X
    - 4333845549584564670108261240787276105
  let C2 : ℤ[X] := 492226908773801810326507618584660359
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
theorem seventeenCertificate_3571 [Fact (Nat.Prime 3571)]
    (hpn : 3571 ≠ 17)
    (hmod : 3571 % 17 = 1) : SeventeenCertificate 3571 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 257
  let Q : ℤ[X] := X^15 - 256*X^14 + 65793*X^13 - 16908800*X^12 + 4345561601*X^11 - 1116809331456*X^10
    + 287019998184193*X^9 - 73764139533337600*X^8 + 18957383860067763201*X^7
    - 4872047652037415142656*X^6 + 1252116246573615691662593*X^5 - 321793875369419232757286400*X^4
    + 82701025969940742818622604801*X^3 - 21254163674274770904386009433856*X^2
    + 5462320064288616122427204424500993*X - 1403816256522174343463791537096755200
  let A : ℤ[X] := 101030741508316663755305075618556731
  let G : ℤ[X] := X^8 + X^4 - 1
  let Qp : ℤ[X] := 152*X^15 + 369*X^14 + 1736*X^13 + 375*X^12 + 194*X^11 + 288*X^10 + 1127*X^9 - 236*X^8
    + 97*X^7 + 220*X^6 + 748*X^5 + 750*X^4 + 236*X^3 + 207*X^2 + 518*X - 847
  let Rp : ℤ[X] := -152*X^7 - 217*X^6 - 1367*X^5 + 1361*X^4 + 29*X^3 - 311*X^2 - 2206*X + 2724
  let QP : ℤ[X] := 11*X^15 + 27*X^14 + 125*X^13 + 27*X^12 + 14*X^11 + 21*X^10 + 81*X^9 - 17*X^8 + 7*X^7
    + 16*X^6 + 54*X^5 + 54*X^4 + 17*X^3 + 15*X^2 + 37*X - 61
  let RP : ℤ[X] := -11*X^7 - 16*X^6 - 98*X^5 + 98*X^4 + 2*X^3 - 23*X^2 - 158*X + 196
  let C1 : ℤ[X] := X^7 - 257*X^6 + 66049*X^5 - 16974593*X^4 + 4362470402*X^3 - 1121154893314*X^2
    + 288136807581698*X - 74051159548496386
  let C2 : ℤ[X] := 5329360964425531
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
theorem seventeenCertificate_3673 [Fact (Nat.Prime 3673)]
    (hpn : 3673 ≠ 17)
    (hmod : 3673 % 17 = 1) : SeventeenCertificate 3673 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 46
  let Q : ℤ[X] := X^15 - 45*X^14 + 2071*X^13 - 95265*X^12 + 4382191*X^11 - 201580785*X^10
    + 9272716111*X^9 - 426544941105*X^8 + 19621067290831*X^7 - 902569095378225*X^6
    + 41518178387398351*X^5 - 1909836205820324145*X^4 + 87852465467734910671*X^3
    - 4041213411515805890865*X^2 + 185895816929727070979791*X - 8551207578767445265070385
  let A : ℤ[X] := 107093805778192889244007
  let G : ℤ[X] := X^15 + X^14 + X^13 + X^11 + X^9 + 2*X^8 + X^4 + X^3 + 2*X^2 + X
  let Qp : ℤ[X] := 3399*X^15 + 1311*X^14 - 1812*X^13 - 1401*X^12 + 1731*X^11 + 906*X^10 - 1547*X^9
    - 2572*X^8 + 502*X^7 + 2345*X^6 - 1627*X^5 - 2565*X^4 + 180*X^3 + 2465*X^2 + 199*X - 2082
  let Rp : ℤ[X] := -3399*X^14 - 1311*X^13 + 1812*X^12 + 4800*X^11 - 3819*X^10 - 630*X^9 - 130*X^8
    - 818*X^7 + 4571*X^6 + 2768*X^5 - 2446*X^4 - 4746*X^3 + 1883*X^2 - 1591*X + 3673
  let QP : ℤ[X] := 42*X^15 + 15*X^14 - 24*X^13 - 18*X^12 + 21*X^11 + 10*X^10 - 21*X^9 - 33*X^8 + 6*X^7
    + 28*X^6 - 22*X^5 - 33*X^4 + 2*X^3 + 30*X^2 + X - 27
  let RP : ℤ[X] := -42*X^14 - 15*X^13 + 24*X^12 + 60*X^11 - 48*X^10 - 7*X^9 - 9*X^7 + 58*X^6 + 34*X^5
    - 31*X^4 - 58*X^3 + 25*X^2 - 18*X + 46
  let C1 : ℤ[X] := X^14 - 45*X^13 + 2071*X^12 - 95266*X^11 + 4382237*X^10 - 201582902*X^9
    + 9272813493*X^8 - 426549420676*X^7 + 19621273351096*X^6 - 902578574150416*X^5
    + 41518614410919136*X^4 - 1909856262902280255*X^3 + 87853388093504891731*X^2
    - 4041255852301225019624*X + 185897769205856350902705
  let C2 : ℤ[X] := -2328150662529102134910
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
theorem seventeenCertificate_3877 [Fact (Nat.Prime 3877)]
    (hpn : 3877 ≠ 17)
    (hmod : 3877 % 17 = 1) : SeventeenCertificate 3877 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 42
  let Q : ℤ[X] := X^15 - 41*X^14 + 1723*X^13 - 72365*X^12 + 3039331*X^11 - 127651901*X^10
    + 5361379843*X^9 - 225177953405*X^8 + 9457474043011*X^7 - 397213909806461*X^6
    + 16682984211871363*X^5 - 700685336898597245*X^4 + 29428784149741084291*X^3
    - 1236008934289125540221*X^2 + 51912375240143272689283*X - 2180319760086017452949885
  let A : ℤ[X] := 23619662090176098278023
  let G : ℤ[X] := -X^13 - X^12 + X^7 - X^5 - X^2
  let Qp : ℤ[X] := -965*X^15 + 795*X^14 + 538*X^13 - 299*X^12 - 38*X^11 + 631*X^10 - 328*X^9 + 1180*X^8
    - 124*X^7 + 366*X^6 - 829*X^5 - 1040*X^4 + 68*X^3 + 56*X^2 + 560*X - 1223
  let Rp : ℤ[X] := -965*X^12 + 795*X^11 + 1503*X^10 - 1094*X^9 - 576*X^8 + 930*X^7 + 675*X^6 - 1211*X^5
    - 504*X^4 + 1783*X^3 - 1223*X^2 - 3877*X + 3877
  let QP : ℤ[X] := -10*X^15 + 9*X^14 + 6*X^13 - 3*X^12 + 7*X^10 - 3*X^9 + 13*X^8 - X^7 + 4*X^6 - 9*X^5
    - 11*X^4 + X^3 + X^2 + 6*X - 13
  let RP : ℤ[X] := -10*X^12 + 9*X^11 + 16*X^10 - 12*X^9 - 6*X^8 + 10*X^7 + 7*X^6 - 13*X^5 - 5*X^4
    + 19*X^3 - 14*X^2 - 41*X + 42
  let C1 : ℤ[X] := -X^12 + 41*X^11 - 1722*X^10 + 72324*X^9 - 3037608*X^8 + 127579536*X^7
    - 5358340511*X^6 + 225050301462*X^5 - 9452112661405*X^4 + 396988731779010*X^3
    - 16673526734718420*X^2 + 700288122858173639*X - 29412101160043292838
  let C2 : ℤ[X] := 318624773980350348
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
theorem seventeenCertificate_3911 [Fact (Nat.Prime 3911)]
    (hpn : 3911 ≠ 17)
    (hmod : 3911 % 17 = 1) : SeventeenCertificate 3911 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 76
  let Q : ℤ[X] := X^15 - 75*X^14 + 5701*X^13 - 433275*X^12 + 32928901*X^11 - 2502596475*X^10
    + 190197332101*X^9 - 14454997239675*X^8 + 1098579790215301*X^7 - 83492064056362875*X^6
    + 6345396868283578501*X^5 - 482250161989551966075*X^4 + 36651012311205949421701*X^3
    - 2785476935651652156049275*X^2 + 211696247109525563859744901*X - 16088914780323942853340612475
  let A : ℤ[X] := 312645748735520239543310291
  let G : ℤ[X] := X^14 - X^12 + X^11 + X^8 + X^7 + X^4 + X^3 + X + 1
  let Qp : ℤ[X] := -227*X^15 + 1381*X^14 + 414*X^13 - 403*X^12 - 887*X^11 + 698*X^10 + 1479*X^9
    + 788*X^8 - 1450*X^7 + 465*X^6 - 368*X^5 + 364*X^4 - 514*X^3 - 273*X^2 + 966*X + 666
  let Rp : ℤ[X] := 227*X^13 - 1608*X^12 + 740*X^11 + 2652*X^10 - 2091*X^9 - 1435*X^8 - 221*X^7
    + 1379*X^6 + 793*X^5 - 1603*X^4 + 814*X^3 + 939*X^2 - 4877*X + 3245
  let QP : ℤ[X] := -4*X^15 + 27*X^14 + 8*X^13 - 8*X^12 - 17*X^11 + 14*X^10 + 29*X^9 + 15*X^8 - 28*X^7
    + 9*X^6 - 7*X^5 + 7*X^4 - 10*X^3 - 5*X^2 + 19*X + 13
  let RP : ℤ[X] := 4*X^13 - 31*X^12 + 15*X^11 + 51*X^10 - 41*X^9 - 28*X^8 - 4*X^7 + 27*X^6 + 15*X^5
    - 31*X^4 + 16*X^3 + 17*X^2 - 94*X + 63
  let C1 : ℤ[X] := X^13 - 76*X^12 + 5775*X^11 - 438899*X^10 + 33356324*X^9 - 2535080624*X^8
    + 192666127425*X^7 - 14642625684299*X^6 + 1112839552006724*X^5 - 84575805952511024*X^4
    + 6427761252390837825*X^3 - 488509855181703674699*X^2 + 37126748993809479277124*X
    - 2821632923529520425061423
  let C2 : ℤ[X] := 54831015645165827743459
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
theorem seventeenCertificate_4013 [Fact (Nat.Prime 4013)]
    (hpn : 4013 ≠ 17)
    (hmod : 4013 % 17 = 1) : SeventeenCertificate 4013 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 10
  let Q : ℤ[X] := X^15 - 9*X^14 + 91*X^13 - 909*X^12 + 9091*X^11 - 90909*X^10 + 909091*X^9 - 9090909*X^8
    + 90909091*X^7 - 909090909*X^6 + 9090909091*X^5 - 90909090909*X^4 + 909090909091*X^3
    - 9090909090909*X^2 + 90909090909091*X - 909090909090909
  let A : ℤ[X] := 2265364837007
  let G : ℤ[X] := -X^15 - 2*X^14 + X^12 - X^11 - 2*X^10 + X^8 - 2*X^6 - X^5 + X^4 + X^3 - 2*X^2 - X + 1
  let Qp : ℤ[X] := -537*X^15 + 820*X^14 - 711*X^13 - 1453*X^12 - 2059*X^11 - 12*X^10 - 417*X^9 - 380*X^8
    - 750*X^7 - 1063*X^6 - 1946*X^5 - 1142*X^4 - 1156*X^3 - 1016*X^2 - 2416*X - 455
  let Rp : ℤ[X] := -537*X^14 + 283*X^13 + 1183*X^12 - 3267*X^11 - 3984*X^10 + 2649*X^9 + 5614*X^8
    - 3434*X^7 - 5790*X^6 + 644*X^5 + 5062*X^4 - 1927*X^3 - 4271*X^2 - 2507*X + 4468
  let QP : ℤ[X] := -X^15 + 2*X^14 - 2*X^13 - 4*X^12 - 5*X^11 - X^9 - X^8 - 2*X^7 - 3*X^6 - 5*X^5 - 3*X^4
    - 3*X^3 - 3*X^2 - 6*X - 1
  let RP : ℤ[X] := -X^14 + X^13 + 2*X^12 - 9*X^11 - 9*X^10 + 8*X^9 + 13*X^8 - 10*X^7 - 14*X^6 + 3*X^5
    + 12*X^4 - 6*X^3 - 11*X^2 - 5*X + 11
  let C1 : ℤ[X] := -X^14 + 8*X^13 - 80*X^12 + 801*X^11 - 8011*X^10 + 80108*X^9 - 801080*X^8
    + 8010801*X^7 - 80108010*X^6 + 801080098*X^5 - 8010800981*X^4 + 80108009811*X^3 - 801080098109*X^2
    + 8010800981088*X - 80108009810881
  let C2 : ℤ[X] := 199621255447
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
theorem seventeenCertificate_4217 [Fact (Nat.Prime 4217)]
    (hpn : 4217 ≠ 17)
    (hmod : 4217 % 17 = 1) : SeventeenCertificate 4217 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 431
  let Q : ℤ[X] := X^15 - 430*X^14 + 185331*X^13 - 79877660*X^12 + 34427271461*X^11 - 14838153999690*X^10
    + 6395244373866391*X^9 - 2756350325136414520*X^8 + 1187986990133794658121*X^7
    - 512022392747665497650150*X^6 + 220681651274243829487214651*X^5 - 95113791699199090508989514580*X^4
    + 40994044222354808009374480783981*X^3 - 17668433059834922252040401217895810*X^2
    + 7615094648788851490629412924913094111*X - 3282105793627994992461276970637543561840
  let A : ℤ[X] := 335448801767528063018925865388850195673
  let G : ℤ[X] := X^12 + X^11 + X^9 + X^8 + X^5 + X^3 + X^2
  let Qp : ℤ[X] := 1456*X^15 + 2253*X^14 + 323*X^13 + 1404*X^12 - 637*X^11 + 1898*X^10 + 1516*X^9
    + 1695*X^8 + 452*X^7 + 626*X^6 + 1538*X^5 + 647*X^4 + 921*X^3 + 903*X^2 + 227*X + 610
  let Rp : ℤ[X] := -1456*X^11 - 2253*X^10 + 1133*X^9 - 607*X^8 - 1293*X^7 + 639*X^6 - 1304*X^5 - 293*X^4
    - 227*X^3 - 610*X^2 - 4217*X + 4217
  let QP : ℤ[X] := 149*X^15 + 230*X^14 + 33*X^13 + 143*X^12 - 65*X^11 + 194*X^10 + 155*X^9 + 173*X^8
    + 46*X^7 + 64*X^6 + 157*X^5 + 66*X^4 + 94*X^3 + 92*X^2 + 23*X + 62
  let RP : ℤ[X] := -149*X^11 - 230*X^10 + 116*X^9 - 62*X^8 - 132*X^7 + 65*X^6 - 133*X^5 - 30*X^4
    - 23*X^3 - 63*X^2 - 430*X + 431
  let C1 : ℤ[X] := X^11 - 430*X^10 + 185330*X^9 - 79877229*X^8 + 34427085700*X^7 - 14838073936700*X^6
    + 6395209866717700*X^5 - 2756335452555328699*X^4 + 1187980580051346669269*X^3
    - 512019630002130414454938*X^2 + 220680460530918208630078279*X - 95113278488825747919563738249
  let C2 : ℤ[X] := 9721086798359947202592357407
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
