import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 8297 through 9623. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_8297 [Fact (Nat.Prime 8297)]
    (hpn : 8297 ≠ 17)
    (hmod : 8297 % 17 = 1) : SeventeenCertificate 8297 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 375
  let Q : ℤ[X] := X^15 - 374*X^14 + 140251*X^13 - 52594124*X^12 + 19722796501*X^11 - 7396048687874*X^10
    + 2773518257952751*X^9 - 1040069346732281624*X^8 + 390026005024605609001*X^7
    - 146259751884227103375374*X^6 + 54847406956585163765765251*X^5 - 20567777608719436412161969124*X^4
    + 7712916603269788654560738421501*X^3 - 2892343726226170745460276908062874*X^2
    + 1084628897334814029547603840523577751*X - 406735836500555261080351440196341656624
  let A : ℤ[X] := 18383263672135497517793394006704606633
  let G : ℤ[X] := X^13 + X^10 + X^9 + X^7 + X^6 + X^5 + X^3 + X^2 + X + 1
  let Qp : ℤ[X] := -2232*X^15 - 3229*X^14 - 2719*X^13 - 3138*X^12 - 3656*X^11 - 237*X^10 - 4624*X^9
    - 2305*X^8 - 745*X^7 - 4955*X^6 - 2635*X^5 - 1450*X^4 - 6084*X^3 - 2407*X^2 - 3980*X - 3192
  let Rp : ℤ[X] := 2232*X^12 + 997*X^11 - 510*X^10 + 2651*X^9 + 3747*X^8 - 2932*X^7 + 6528*X^6
    + 1847*X^5 - 1742*X^4 + 6084*X^3 + 2407*X^2 - 4317*X + 11489
  let QP : ℤ[X] := -101*X^15 - 146*X^14 - 123*X^13 - 142*X^12 - 165*X^11 - 11*X^10 - 209*X^9 - 104*X^8
    - 34*X^7 - 224*X^6 - 119*X^5 - 66*X^4 - 275*X^3 - 109*X^2 - 180*X - 144
  let RP : ℤ[X] := 101*X^12 + 45*X^11 - 23*X^10 + 120*X^9 + 169*X^8 - 132*X^7 + 295*X^6 + 83*X^5
    - 78*X^4 + 275*X^3 + 108*X^2 - 194*X + 519
  let C1 : ℤ[X] := X^12 - 375*X^11 + 140625*X^10 - 52734374*X^9 + 19775390251*X^8 - 7415771344125*X^7
    + 2780914254046876*X^6 - 1042842845267578499*X^5 + 391066066975341937126*X^4
    - 146649775115753226422250*X^3 + 54993665668407459908343751*X^2 - 20622624625652797465628906624*X
    + 7733484234619799049610839984001
  let C2 : ℤ[X] := -349530744604365992961801252742
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
theorem seventeenCertificate_8467 [Fact (Nat.Prime 8467)]
    (hpn : 8467 ≠ 17)
    (hmod : 8467 % 17 = 1) : SeventeenCertificate 8467 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 125
  let Q : ℤ[X] := X^15 - 124*X^14 + 15501*X^13 - 1937624*X^12 + 242203001*X^11 - 30275375124*X^10
    + 3784421890501*X^9 - 473052736312624*X^8 + 59131592039078001*X^7 - 7391449004884750124*X^6
    + 923931125610593765501*X^5 - 115491390701324220687624*X^4 + 14436423837665527585953001*X^3
    - 1804552979708190948244125124*X^2 + 225569122463523868530515640501*X
    - 28196140307940483566314455062624
  let A : ℤ[X] := 416265210640434681208138287803
  let G : ℤ[X] := X^13 + X^9 - X^7 - X^2 + X + 1
  let Qp : ℤ[X] := -2055*X^15 + 810*X^14 - 1701*X^13 - 1105*X^12 + 598*X^11 - 602*X^10 - 3008*X^9
    + 1397*X^8 + 1127*X^7 + 1009*X^6 - 1175*X^5 + 881*X^4 - 2109*X^3 - 907*X^2 + 1249*X + 2693
  let Rp : ℤ[X] := 2055*X^12 - 2865*X^11 + 2511*X^10 - 596*X^9 + 352*X^8 - 1665*X^7 + 2862*X^6
    - 2136*X^5 - 3944*X^4 + 1914*X^3 + 6293*X^2 - 9716*X + 5774
  let QP : ℤ[X] := -30*X^15 + 12*X^14 - 25*X^13 - 16*X^12 + 9*X^11 - 9*X^10 - 44*X^9 + 21*X^8 + 17*X^7
    + 15*X^6 - 17*X^5 + 13*X^4 - 31*X^3 - 13*X^2 + 19*X + 40
  let RP : ℤ[X] := 30*X^12 - 42*X^11 + 37*X^10 - 9*X^9 + 5*X^8 - 24*X^7 + 42*X^6 - 32*X^5 - 58*X^4
    + 29*X^3 + 92*X^2 - 143*X + 85
  let C1 : ℤ[X] := X^12 - 125*X^11 + 15625*X^10 - 1953125*X^9 + 244140626*X^8 - 30517578250*X^7
    + 3814697281249*X^6 - 476837160156125*X^5 + 59604645019515625*X^4 - 7450580627439453125*X^3
    + 931322578429931640625*X^2 - 116415322303741455078126*X + 14551915287967681884765751
  let C2 : ℤ[X] := -214832811030584650477822
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
theorem seventeenCertificate_8501 [Fact (Nat.Prime 8501)]
    (hpn : 8501 ≠ 17)
    (hmod : 8501 % 17 = 1) : SeventeenCertificate 8501 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 317
  let Q : ℤ[X] := X^15 - 316*X^14 + 100173*X^13 - 31754840*X^12 + 10066284281*X^11 - 3191012117076*X^10
    + 1011550841113093*X^9 - 320661616632850480*X^8 + 101649732472613602161*X^7
    - 32222965193818511885036*X^6 + 10214679966440468267556413*X^5 - 3238053549361628440815382920*X^4
    + 1026462975147636215738476385641*X^3 - 325388763121800680389097014248196*X^2
    + 103148237909610815683343753516678133*X - 32697991417346628571619969864786968160
  let A : ℤ[X] := 1219299291765543025197450940729028221
  let G : ℤ[X] := X^9 - X^8 + X^5 + X^4 + 1
  let Qp : ℤ[X] := 983*X^15 + 3909*X^14 + 2976*X^13 + 1202*X^12 + 2494*X^11 + 978*X^10 - 3007*X^9
    + 2090*X^8 + 1531*X^7 + 213*X^6 + 1470*X^5 + 2548*X^4 + 862*X^3 - 239*X^2 + 237*X + 2363
  let Rp : ℤ[X] := -983*X^8 - 1943*X^7 + 3859*X^6 + 841*X^5 - 4049*X^4 - 1101*X^3 + 476*X^2 - 6375*X + 6138
  let QP : ℤ[X] := 37*X^15 + 146*X^14 + 111*X^13 + 45*X^12 + 93*X^11 + 36*X^10 - 112*X^9 + 78*X^8
    + 57*X^7 + 8*X^6 + 55*X^5 + 95*X^4 + 32*X^3 - 9*X^2 + 9*X + 88
  let RP : ℤ[X] := -37*X^8 - 72*X^7 + 144*X^6 + 31*X^5 - 151*X^4 - 41*X^3 + 17*X^2 - 237*X + 229
  let C1 : ℤ[X] := X^8 - 318*X^7 + 100806*X^6 - 31955502*X^5 + 10129894135*X^4 - 3211176440794*X^3
    + 1017942931731698*X^2 - 322687909358948266*X + 102292067266786600322
  let C2 : ℤ[X] := -3814443632933931573
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
theorem seventeenCertificate_8807 [Fact (Nat.Prime 8807)]
    (hpn : 8807 ≠ 17)
    (hmod : 8807 % 17 = 1) : SeventeenCertificate 8807 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 28
  let Q : ℤ[X] := X^15 - 27*X^14 + 757*X^13 - 21195*X^12 + 593461*X^11 - 16616907*X^10 + 465273397*X^9
    - 13027655115*X^8 + 364774343221*X^7 - 10213681610187*X^6 + 285983085085237*X^5
    - 8007526382386635*X^4 + 224210738706825781*X^3 - 6277900683791121867*X^2 + 175781219146151412277*X
    - 4921874136092239543755
  let A : ℤ[X] := 15648061293355592963
  let G : ℤ[X] := X^12 + X^9 + X^8 + X^7 + X^5 + X^2 + 1
  let Qp : ℤ[X] := 2594*X^15 + 418*X^14 - 303*X^13 + 2271*X^12 + 655*X^11 + 1868*X^10 + 3132*X^9
    + 2968*X^8 - 1247*X^7 + 2282*X^6 + 347*X^5 + 1685*X^4 - 551*X^3 + 408*X^2 - 23*X + 3238
  let Rp : ℤ[X] := -2594*X^11 + 2176*X^10 + 721*X^9 - 5168*X^8 + 1198*X^7 - 910*X^6 - 941*X^5 - 2667*X^4
    + 4220*X^3 - 3669*X^2 - 5546*X + 5569
  let QP : ℤ[X] := 8*X^15 + X^14 - X^13 + 7*X^12 + 2*X^11 + 6*X^10 + 10*X^9 + 9*X^8 - 4*X^7 + 7*X^6
    + X^5 + 5*X^4 - 2*X^3 + X^2 + 10
  let RP : ℤ[X] := -8*X^11 + 7*X^10 + 2*X^9 - 16*X^8 + 4*X^7 - 3*X^6 - 3*X^5 - 8*X^4 + 13*X^3 - 12*X^2
    - 17*X + 18
  let C1 : ℤ[X] := X^11 - 28*X^10 + 784*X^9 - 21951*X^8 + 614629*X^7 - 17209611*X^6 + 481869108*X^5
    - 13492335023*X^4 + 377785380644*X^3 - 10577990658032*X^2 + 296183738424897*X - 8293144675897116
  let C2 : ℤ[X] := 26366305316807
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
theorem seventeenCertificate_9011 [Fact (Nat.Prime 9011)]
    (hpn : 9011 ≠ 17)
    (hmod : 9011 % 17 = 1) : SeventeenCertificate 9011 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 348
  let Q : ℤ[X] := X^15 - 347*X^14 + 120757*X^13 - 42023435*X^12 + 14624155381*X^11 - 5089206072587*X^10
    + 1771043713260277*X^9 - 616323212214576395*X^8 + 214480477850672585461*X^7
    - 74639206292034059740427*X^6 + 25974443789627852789668597*X^5 - 9039106438790492770804671755*X^4
    + 3145609040699091484240025770741*X^3 - 1094671946163283836515528968217867*X^2
    + 380945837264822775107404080939817717*X - 132569151368158325737376620167056565515
  let A : ℤ[X] := 5119749714362345728177456865845709111
  let G : ℤ[X] := X^12 + X^11 + X^10 + X^7 + X^3 + 1
  let Qp : ℤ[X] := -2888*X^15 + 1915*X^14 - 2494*X^13 - 32*X^12 - 763*X^11 + 1317*X^10 - 1643*X^9
    + 1183*X^8 - 66*X^7 + 2058*X^6 + 1808*X^5 - 1302*X^4 - 342*X^3 - 1015*X^2 - 1097*X + 406
  let Rp : ℤ[X] := 2888*X^11 - 1915*X^10 + 2494*X^9 - 2856*X^8 + 2678*X^7 - 923*X^6 - 3192*X^5
    + 2463*X^4 - 1079*X^3 - 82*X^2 - 7508*X + 8605
  let QP : ℤ[X] := -111*X^15 + 74*X^14 - 96*X^13 - X^12 - 29*X^11 + 51*X^10 - 63*X^9 + 46*X^8 - 2*X^7
    + 80*X^6 + 70*X^5 - 50*X^4 - 13*X^3 - 39*X^2 - 42*X + 16
  let RP : ℤ[X] := 111*X^11 - 74*X^10 + 96*X^9 - 110*X^8 + 103*X^7 - 36*X^6 - 123*X^5 + 95*X^4 - 42*X^3
    - 4*X^2 - 289*X + 332
  let C1 : ℤ[X] := X^11 - 347*X^10 + 120757*X^9 - 42023436*X^8 + 14624155728*X^7 - 5089206193343*X^6
    + 1771043755283364*X^5 - 616323226838610672*X^4 + 214480482939836513856*X^3
    - 74639208063063106821887*X^2 + 25974444405945961174016676*X - 9039106653269194488557803248
  let C2 : ℤ[X] := 349085463914957239154157755
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
theorem seventeenCertificate_9181 [Fact (Nat.Prime 9181)]
    (hpn : 9181 ≠ 17)
    (hmod : 9181 % 17 = 1) : SeventeenCertificate 9181 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 347
  let Q : ℤ[X] := X^15 - 346*X^14 + 120063*X^13 - 41661860*X^12 + 14456665421*X^11 - 5016462901086*X^10
    + 1740712626676843*X^9 - 604027281456864520*X^8 + 209597466665531988441*X^7
    - 72730320932939599989026*X^6 + 25237421363730041196192023*X^5 - 8757385213214324295078631980*X^4
    + 3038812668985370530392285297061*X^3 - 1054467996137923574046122998080166*X^2
    + 365900394659859480194004680333817603*X - 126967436946971239627319624075834708240
  let A : ℤ[X] := 4798791048970593633665168233777872101
  let G : ℤ[X] := -X^12 - X^11 - X^9 + X^8 - X^5 - X^3 - X^2 - 1
  let Qp : ℤ[X] := -5358*X^15 - 694*X^14 + 5935*X^13 + 922*X^12 - 3957*X^11 - 248*X^10 + 7250*X^9
    + 3667*X^8 - 1648*X^7 - 2724*X^6 + 3408*X^5 + 5596*X^4 - 798*X^3 - 3882*X^2 + 1270*X + 3821
  let Rp : ℤ[X] := -5358*X^11 - 694*X^10 + 11293*X^9 - 3742*X^8 + 130*X^7 + 795*X^6 - 435*X^5 - 1309*X^4
    + 4354*X^3 - 1331*X^2 - 11732*X + 13002
  let QP : ℤ[X] := -202*X^15 - 25*X^14 + 225*X^13 + 35*X^12 - 149*X^11 - 8*X^10 + 275*X^9 + 139*X^8
    - 62*X^7 - 102*X^6 + 130*X^5 + 212*X^4 - 30*X^3 - 146*X^2 + 49*X + 145
  let RP : ℤ[X] := -202*X^11 - 25*X^10 + 427*X^9 - 142*X^8 + 5*X^7 + 30*X^6 - 16*X^5 - 49*X^4 + 165*X^3
    - 51*X^2 - 442*X + 492
  let C1 : ℤ[X] := -X^11 + 346*X^10 - 120062*X^9 + 41661513*X^8 - 14456545010*X^7 + 5016421118470*X^6
    - 1740698128109090*X^5 + 604022250453854229*X^4 - 209595720907487417463*X^3
    + 72729715154898133859660*X^2 - 25237211158749652449302021*X + 8757312272086129399907801287
  let C2 : ℤ[X] := -330986532884640769171986390
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
theorem seventeenCertificate_9283 [Fact (Nat.Prime 9283)]
    (hpn : 9283 ≠ 17)
    (hmod : 9283 % 17 = 1) : SeventeenCertificate 9283 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 398
  let Q : ℤ[X] := X^15 - 397*X^14 + 158007*X^13 - 62886785*X^12 + 25028940431*X^11 - 9961518291537*X^10
    + 3964684280031727*X^9 - 1577944343452627345*X^8 + 628021848694145683311*X^7
    - 249952695780269981957777*X^6 + 99481172920547452819195247*X^5 - 39593506822377886222039708305*X^4
    + 15758215715306398716371803905391*X^3 - 6271769854691946689115977954345617*X^2
    + 2496164402167394782268159225829555567*X - 993473432062623123342727371880163115665
  let A : ℤ[X] := 42594250345892922879500753421125166437
  let G : ℤ[X] := X^10 - X^7 - X^4 - X^3 - 1
  let Qp : ℤ[X] := -1049*X^15 - 1282*X^14 - 1378*X^13 - 302*X^12 - 1532*X^11 - 3991*X^10 - 24*X^9
    - 780*X^8 + 3052*X^7 + 328*X^6 - 1631*X^5 - 1721*X^4 - 3033*X^3 - 705*X^2 + 1051*X - 1612
  let Rp : ℤ[X] := 1049*X^9 + 233*X^8 + 96*X^7 - 2125*X^6 + 997*X^5 + 2363*X^4 - 3940*X^3 - 1756*X^2
    - 6620*X + 7671
  let QP : ℤ[X] := -45*X^15 - 55*X^14 - 59*X^13 - 13*X^12 - 66*X^11 - 171*X^10 - X^9 - 33*X^8 + 131*X^7
    + 14*X^6 - 70*X^5 - 74*X^4 - 130*X^3 - 30*X^2 + 45*X - 69
  let RP : ℤ[X] := 45*X^9 + 10*X^8 + 4*X^7 - 91*X^6 + 43*X^5 + 101*X^4 - 169*X^3 - 76*X^2 - 283*X + 329
  let C1 : ℤ[X] := X^9 - 398*X^8 + 158404*X^7 - 63044793*X^6 + 25091827614*X^5 - 9986547390372*X^4
    + 3974645861368055*X^3 - 1581909052824485891*X^2 + 629599803024145384618*X
    - 250580721603609863077964
  let C2 : ℤ[X] := 10743415619760500431437
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
theorem seventeenCertificate_9419 [Fact (Nat.Prime 9419)]
    (hpn : 9419 ≠ 17)
    (hmod : 9419 % 17 = 1) : SeventeenCertificate 9419 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 55
  let Q : ℤ[X] := X^15 - 54*X^14 + 2971*X^13 - 163404*X^12 + 8987221*X^11 - 494297154*X^10
    + 27186343471*X^9 - 1495248890904*X^8 + 82238688999721*X^7 - 4523127894984654*X^6
    + 248772034224155971*X^5 - 13682461882328578404*X^4 + 752535403528071812221*X^3
    - 41389447194043949672154*X^2 + 2276419595672417231968471*X - 125203077761982947758265904
  let A : ℤ[X] := 731093457576076242351059
  let G : ℤ[X] := X^15 + X^13 + X^12 + X^11 + X^9 + 2*X^7 + X^5 + X
  let Qp : ℤ[X] := 3272*X^15 + 2273*X^14 + 704*X^13 + 2228*X^12 + 3179*X^11 + 7388*X^10 + 1949*X^9
    - 314*X^8 + 1704*X^7 + 3742*X^6 + 4680*X^5 + 185*X^4 + 2516*X^3 + 6177*X^2 + 2621*X + 402
  let Rp : ℤ[X] := -3272*X^14 + 999*X^13 - 1703*X^12 - 3797*X^11 - 1655*X^10 - 3165*X^9 + 1261*X^8
    - 3422*X^7 - 6714*X^6 + 1929*X^5 + 3661*X^4 - 3556*X^3 - 2219*X^2 - 9821*X + 9419
  let QP : ℤ[X] := 19*X^15 + 13*X^14 + 4*X^13 + 13*X^12 + 19*X^11 + 43*X^10 + 11*X^9 - 2*X^8 + 10*X^7
    + 22*X^6 + 27*X^5 + X^4 + 15*X^3 + 36*X^2 + 15*X + 2
  let RP : ℤ[X] := -19*X^14 + 6*X^13 - 10*X^12 - 22*X^11 - 10*X^10 - 18*X^9 + 7*X^8 - 20*X^7 - 39*X^6
    + 12*X^5 + 21*X^4 - 21*X^3 - 14*X^2 - 56*X + 55
  let C1 : ℤ[X] := X^14 - 55*X^13 + 3026*X^12 - 166429*X^11 + 9153596*X^10 - 503447780*X^9
    + 27689627901*X^8 - 1522929534555*X^7 + 83761124400527*X^6 - 4606861842028985*X^5
    + 253377401311594176*X^4 - 13935757072137679680*X^3 + 766466638967572382400*X^2
    - 42155665143216481032000*X + 2318561582876906456760001
  let C2 : ℤ[X] := -13538686384778623539845
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
theorem seventeenCertificate_9521 [Fact (Nat.Prime 9521)]
    (hpn : 9521 ≠ 17)
    (hmod : 9521 % 17 = 1) : SeventeenCertificate 9521 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 506
  let Q : ℤ[X] := X^15 - 505*X^14 + 255531*X^13 - 129298685*X^12 + 65425134611*X^11
    - 33105118113165*X^10 + 16751189765261491*X^9 - 8476102021222314445*X^8 + 4288907622738491109171*X^7
    - 2170187257105676501240525*X^6 + 1098114752095472309627705651*X^5
    - 555646064560308988671619059405*X^4 + 281156908667516348267839244058931*X^3
    - 142265395785763272223526657493819085*X^2 + 71986290267596215745104488691872457011*X
    - 36425062875403685167022871278087463247565
  let A : ℤ[X] := 1935834661795427444019911024757090263971
  let G : ℤ[X] := X^14 + X^13 + X^12 + X^7 + X^6 - X^5 + X^4 + X
  let Qp : ℤ[X] := -3773*X^15 + 1165*X^14 + 6560*X^13 - 304*X^12 - 2285*X^11 + 396*X^10 + 5313*X^9
    + 2292*X^8 - 1963*X^7 - 679*X^6 + 6566*X^5 + 6181*X^4 + 1050*X^3 - 1897*X^2 + 4009*X + 5167
  let Rp : ℤ[X] := 3773*X^13 - 1165*X^12 - 6560*X^11 - 3469*X^10 + 3450*X^9 + 6164*X^8 - 5617*X^7
    - 804*X^6 + 1194*X^5 - 8114*X^4 + 5906*X^3 + 1158*X^2 - 14688*X + 9521
  let QP : ℤ[X] := -200*X^15 + 63*X^14 + 349*X^13 - 16*X^12 - 121*X^11 + 22*X^10 + 283*X^9 + 122*X^8
    - 104*X^7 - 35*X^6 + 350*X^5 + 329*X^4 + 56*X^3 - 100*X^2 + 214*X + 275
  let RP : ℤ[X] := 200*X^13 - 63*X^12 - 349*X^11 - 184*X^10 + 184*X^9 + 327*X^8 - 299*X^7 - 43*X^6
    + 63*X^5 - 431*X^4 + 314*X^3 + 60*X^2 - 780*X + 506
  let C1 : ℤ[X] := X^13 - 505*X^12 + 255531*X^11 - 129298686*X^10 + 65425135116*X^9 - 33105118368696*X^8
    + 16751189894560176*X^7 - 8476102086647449055*X^6 + 4288907655843609221831*X^5
    - 2170187273856866266246487*X^4 + 1098114760571574330720722423*X^3
    - 555646068849216611344685546038*X^2 + 281156910837703605340410886295228*X
    - 142265396883878024302247908465385367
  let C2 : ℤ[X] := 7560790969776523505612587089957462
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
theorem seventeenCertificate_9623 [Fact (Nat.Prime 9623)]
    (hpn : 9623 ≠ 17)
    (hmod : 9623 % 17 = 1) : SeventeenCertificate 9623 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 123
  let Q : ℤ[X] := X^15 - 122*X^14 + 15007*X^13 - 1845860*X^12 + 227040781*X^11 - 27926016062*X^10
    + 3434899975627*X^9 - 422492697002120*X^8 + 51966601731260761*X^7 - 6391892012945073602*X^6
    + 786202717592244053047*X^5 - 96702934263846018524780*X^4 + 11894460914453060278547941*X^3
    - 1463018692477726414261396742*X^2 + 179951299174760348954151799267*X
    - 22134009798495522921360671309840
  let A : ℤ[X] := 282914185307591117045345793527
  let G : ℤ[X] := X^6 + X^3 + X^2 + 2
  let Qp : ℤ[X] := 5929*X^15 + 8010*X^14 + 2245*X^13 - 762*X^12 + 3425*X^11 + 8066*X^10 + 4980*X^9
    - 362*X^8 + 2340*X^7 + 6799*X^6 + 6853*X^5 + 211*X^4 - 778*X^3 + 5393*X^2 + 6577*X + 5290
  let Rp : ℤ[X] := -5929*X^5 - 2081*X^4 + 5765*X^3 - 2922*X^2 - 12197*X - 957
  let QP : ℤ[X] := 76*X^15 + 102*X^14 + 28*X^13 - 10*X^12 + 44*X^11 + 103*X^10 + 63*X^9 - 5*X^8 + 30*X^7
    + 87*X^6 + 87*X^5 + 2*X^4 - 10*X^3 + 69*X^2 + 84*X + 67
  let RP : ℤ[X] := -76*X^5 - 26*X^4 + 74*X^3 - 38*X^2 - 156*X - 11
  let C1 : ℤ[X] := X^5 - 123*X^4 + 15129*X^3 - 1860866*X^2 + 228886519*X - 28153041837
  let C2 : ℤ[X] := 359848711
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
