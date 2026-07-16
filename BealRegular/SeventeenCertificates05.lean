import BealRegular.SeventeenCertificateBase

/-! Exact polynomial certificates for p = 17, rational primes 6053 through 6971. -/

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem seventeenCertificate_6053 [Fact (Nat.Prime 6053)]
    (hpn : 6053 ≠ 17)
    (hmod : 6053 % 17 = 1) : SeventeenCertificate 6053 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 357
  let Q : ℤ[X] := X^15 - 356*X^14 + 127093*X^13 - 45372200*X^12 + 16197875401*X^11 - 5782641518156*X^10
    + 2064403021981693*X^9 - 736991878847464400*X^8 + 263106100748544790801*X^7
    - 93928877967230490315956*X^6 + 33532609434301285042796293*X^5 - 11971141568045558760278276600*X^4
    + 4273697539792264477419344746201*X^3 - 1525710021705838418438706074393756*X^2
    + 544678477748984315382618068558570893*X - 194450216556387400591594650475409808800
  let A : ℤ[X] := 11468482952359210641202592139388947917
  let G : ℤ[X] := X^15 + X^14 + X^12 + X^11 + X^9 + X^7 + X^6 + X^5 + 2*X^4 + X^3 + X
  let Qp : ℤ[X] := 2459*X^15 + 2281*X^14 - 756*X^13 - 34*X^12 + 2491*X^11 + 2963*X^10 - 2110*X^9
    - 896*X^8 + 1522*X^7 + 3875*X^6 - 832*X^5 - 3167*X^4 + 1167*X^3 + 3497*X^2 + 948*X - 3062
  let Rp : ℤ[X] := -2459*X^14 - 2281*X^13 + 3215*X^12 - 144*X^11 - 5528*X^10 + 218*X^9 + 4457*X^8
    + 790*X^7 - 6051*X^6 - 3173*X^5 + 4444*X^4 + 513*X^3 - 4010*X^2 - 2991*X + 6053
  let QP : ℤ[X] := 145*X^15 + 134*X^14 - 45*X^13 - 2*X^12 + 147*X^11 + 174*X^10 - 125*X^9 - 53*X^8
    + 90*X^7 + 228*X^6 - 50*X^5 - 187*X^4 + 69*X^3 + 206*X^2 + 55*X - 181
  let RP : ℤ[X] := -145*X^14 - 134*X^13 + 190*X^12 - 9*X^11 - 326*X^10 + 14*X^9 + 263*X^8 + 46*X^7
    - 357*X^6 - 186*X^5 + 263*X^4 + 30*X^3 - 237*X^2 - 175*X + 357
  let C1 : ℤ[X] := X^14 - 356*X^13 + 127092*X^12 - 45371843*X^11 + 16197747952*X^10 - 5782596018864*X^9
    + 2064386778734449*X^8 - 736986080008198293*X^7 + 263104030562926790602*X^6
    - 93928138910964864244913*X^5 + 33532345591214456535433942*X^4 - 11971047376063560983149917292*X^3
    + 4273663913254691270984520473245*X^2 - 1525698017031924783741473808948465*X
    + 544674192080397147795706149794602006
  let C2 : ℤ[X] := -32124349342921160046764760528113814
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
theorem seventeenCertificate_6121 [Fact (Nat.Prime 6121)]
    (hpn : 6121 ≠ 17)
    (hmod : 6121 % 17 = 1) : SeventeenCertificate 6121 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 142
  let Q : ℤ[X] := X^15 - 141*X^14 + 20023*X^13 - 2843265*X^12 + 403743631*X^11 - 57331595601*X^10
    + 8141086575343*X^9 - 1156034293698705*X^8 + 164156869705216111*X^7 - 23310275498140687761*X^6
    + 3310059120735977662063*X^5 - 470028395144508828012945*X^4 + 66744032110520253577838191*X^3
    - 9477652559693876008053023121*X^2 + 1345826663476530393143529283183*X
    - 191107386213667315826381158211985
  let A : ℤ[X] := 4433466564669295678377082905751
  let G : ℤ[X] := X^13 + X^11 + X^9 + X^8 + X^5 + X^4 + X^3 + 1
  let Qp : ℤ[X] := -1271*X^15 + 1702*X^14 + 1885*X^13 + 383*X^12 - 568*X^11 - 188*X^10 + 941*X^9
    - 231*X^8 + 926*X^7 + 1899*X^6 - 1605*X^5 + 162*X^4 + 209*X^3 - 344*X^2 - 1391*X + 379
  let Rp : ℤ[X] := 1271*X^12 - 2973*X^11 + 1088*X^10 - 1471*X^9 + 2039*X^8 - 580*X^7 - 3334*X^6
    + 2111*X^5 + 1438*X^4 - 932*X^3 - 1047*X^2 - 4351*X + 5742
  let QP : ℤ[X] := -29*X^15 + 40*X^14 + 44*X^13 + 9*X^12 - 13*X^11 - 4*X^10 + 22*X^9 - 5*X^8 + 22*X^7
    + 44*X^6 - 37*X^5 + 4*X^4 + 5*X^3 - 8*X^2 - 32*X + 9
  let RP : ℤ[X] := 29*X^12 - 69*X^11 + 25*X^10 - 34*X^9 + 47*X^8 - 14*X^7 - 77*X^6 + 49*X^5 + 33*X^4
    - 22*X^3 - 25*X^2 - 100*X + 133
  let C1 : ℤ[X] := X^12 - 142*X^11 + 20165*X^10 - 2863430*X^9 + 406607061*X^8 - 57738202661*X^7
    + 8198824777862*X^6 - 1164233118456404*X^5 + 165321102820809369*X^4 - 23475596600554930397*X^3
    + 3333534717278800116375*X^2 - 473361929853589616525250*X + 67217394039209725546585500
  let C2 : ℤ[X] := -1559364475341901817940719
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
theorem seventeenCertificate_6257 [Fact (Nat.Prime 6257)]
    (hpn : 6257 ≠ 17)
    (hmod : 6257 % 17 = 1) : SeventeenCertificate 6257 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 88
  let Q : ℤ[X] := X^15 - 87*X^14 + 7657*X^13 - 673815*X^12 + 59295721*X^11 - 5218023447*X^10
    + 459186063337*X^9 - 40408373573655*X^8 + 3555936874481641*X^7 - 312922444954384407*X^6
    + 27537175155985827817*X^5 - 2423271413726752847895*X^4 + 213247884407954250614761*X^3
    - 18765813827899974054098967*X^2 + 1651391616855197716760709097*X - 145322462283257399074942400535
  let A : ℤ[X] := 2043851155653931775386755833
  let G : ℤ[X] := X^6 + X^2 + X - 1
  let Qp : ℤ[X] := -130*X^15 - 1204*X^14 - 547*X^13 - 2050*X^12 - 1183*X^11 - 2395*X^10 - 2108*X^9
    - 2336*X^8 - 1043*X^7 - 2201*X^6 - 409*X^5 - 1680*X^4 - 2458*X^3 - 2821*X^2 - 2162*X - 3841
  let Rp : ℤ[X] := 130*X^5 + 1074*X^4 - 657*X^3 + 1503*X^2 - 737*X + 2416
  let QP : ℤ[X] := -2*X^15 - 17*X^14 - 8*X^13 - 29*X^12 - 17*X^11 - 34*X^10 - 30*X^9 - 33*X^8 - 15*X^7
    - 31*X^6 - 6*X^5 - 24*X^4 - 35*X^3 - 40*X^2 - 31*X - 54
  let RP : ℤ[X] := 2*X^5 + 15*X^4 - 9*X^3 + 21*X^2 - 10*X + 34
  let C1 : ℤ[X] := X^5 - 88*X^4 + 7744*X^3 - 681472*X^2 + 59969537*X - 5277319255
  let C2 : ℤ[X] := 74221527
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
theorem seventeenCertificate_6359 [Fact (Nat.Prime 6359)]
    (hpn : 6359 ≠ 17)
    (hmod : 6359 % 17 = 1) : SeventeenCertificate 6359 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 193
  let Q : ℤ[X] := X^15 - 192*X^14 + 37057*X^13 - 7152000*X^12 + 1380336001*X^11 - 266404848192*X^10
    + 51416135701057*X^9 - 9923314190304000*X^8 + 1915199638728672001*X^7 - 369633530274633696192*X^6
    + 71339271343004303365057*X^5 - 13768479369199830549456000*X^4 + 2657316518255567296045008001*X^3
    - 512862088023324488136686544192*X^2 + 98982382988501626210380503029057*X
    - 19103599916780813858603437084608000
  let A : ℤ[X] := 579807325670498046030895322744039
  let G : ℤ[X] := X^13 + X^11 + X^10 + X^7 + X^5 + X^4 + X^2 + 1
  let Qp : ℤ[X] := -389*X^15 - 1620*X^14 + 680*X^13 + 1910*X^12 - 197*X^11 - 522*X^10 - 1387*X^9
    + 224*X^8 + 892*X^7 - 852*X^6 - 1287*X^5 + X^4 - 582*X^3 - 2525*X^2 - 2707*X + 624
  let Rp : ℤ[X] := 389*X^12 + 1231*X^11 - 1911*X^10 + 390*X^9 + 1038*X^8 - 3205*X^7 + 2131*X^6
    + 2052*X^5 - 1389*X^4 + 1388*X^3 - 806*X^2 - 3028*X + 5735
  let QP : ℤ[X] := -12*X^15 - 49*X^14 + 21*X^13 + 58*X^12 - 6*X^11 - 16*X^10 - 42*X^9 + 7*X^8 + 27*X^7
    - 26*X^6 - 39*X^5 - 18*X^3 - 77*X^2 - 82*X + 19
  let RP : ℤ[X] := 12*X^12 + 37*X^11 - 58*X^10 + 12*X^9 + 31*X^8 - 97*X^7 + 65*X^6 + 62*X^5 - 42*X^4
    + 42*X^3 - 25*X^2 - 91*X + 174
  let C1 : ℤ[X] := X^12 - 193*X^11 + 37250*X^10 - 7189249*X^9 + 1387525057*X^8 - 267792336001*X^7
    + 51683920848194*X^6 - 9974996723701442*X^5 + 1925174367674378307*X^4 - 371558652961155013250*X^3
    + 71710820021502917557250*X^2 - 13840188264150063088549249*X + 2671156334980962176090005057
  let C2 : ℤ[X] := -81071422024111605596064000
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
theorem seventeenCertificate_6427 [Fact (Nat.Prime 6427)]
    (hpn : 6427 ≠ 17)
    (hmod : 6427 % 17 = 1) : SeventeenCertificate 6427 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 111
  let Q : ℤ[X] := X^15 - 110*X^14 + 12211*X^13 - 1355420*X^12 + 150451621*X^11 - 16700129930*X^10
    + 1853714422231*X^9 - 205762300867640*X^8 + 22839615396308041*X^7 - 2535197308990192550*X^6
    + 281406901297911373051*X^5 - 31236166044068162408660*X^4 + 3467214430891566027361261*X^3
    - 384860801828963829037099970*X^2 + 42719549003014985023118096671*X
    - 4741869939334663337566108730480
  let A : ℤ[X] := 81896306716375856615814232003
  let G : ℤ[X] := X^15 + X^14 + 2*X^13 + X^12 + 2*X^11 + 2*X^10 + X^8 + 2*X^7 + X^6 + X^5 + 2*X^4 + X^3
    + X^2 + X + 2
  let Qp : ℤ[X] := 3790*X^15 + 7282*X^14 + 5290*X^13 + 1457*X^12 + 2738*X^11 + 8368*X^10 + 6857*X^9
    + 1049*X^8 + 3037*X^7 + 7314*X^6 + 8165*X^5 + 3682*X^4 - 11*X^3 + 5011*X^2 + 6718*X + 3624
  let Rp : ℤ[X] := -3790*X^14 - 7282*X^13 - 9080*X^12 - 4949*X^11 - 4536*X^10 - 11817*X^9 - 5848*X^8
    + 2638*X^7 - 4756*X^6 - 15742*X^5 - 10999*X^4 + 5033*X^3 - 3304*X^2 - 16239*X - 821
  let QP : ℤ[X] := 66*X^15 + 126*X^14 + 91*X^13 + 25*X^12 + 48*X^11 + 145*X^10 + 118*X^9 + 18*X^8
    + 53*X^7 + 127*X^6 + 141*X^5 + 63*X^4 + 87*X^2 + 116*X + 62
  let RP : ℤ[X] := -66*X^14 - 126*X^13 - 157*X^12 - 85*X^11 - 79*X^10 - 205*X^9 - 100*X^8 + 46*X^7
    - 84*X^6 - 273*X^5 - 188*X^4 + 87*X^3 - 59*X^2 - 280*X - 13
  let C1 : ℤ[X] := X^14 - 110*X^13 + 12212*X^12 - 1355531*X^11 + 150463943*X^10 - 16701497671*X^9
    + 1853866241481*X^8 - 205779152804390*X^7 + 22841485961287292*X^6 - 2535404941702889411*X^5
    + 281429948529020724622*X^4 - 31238724286721300433040*X^3 + 3467498395826064348067441*X^2
    - 384892321936693142635485950*X + 42723047734972938832538940451
  let C2 : ℤ[X] := -737864991221720275464730417
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
theorem seventeenCertificate_6529 [Fact (Nat.Prime 6529)]
    (hpn : 6529 ≠ 17)
    (hmod : 6529 % 17 = 1) : SeventeenCertificate 6529 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 8
  let Q : ℤ[X] := X^15 - 7*X^14 + 57*X^13 - 455*X^12 + 3641*X^11 - 29127*X^10 + 233017*X^9 - 1864135*X^8
    + 14913081*X^7 - 119304647*X^6 + 954437177*X^5 - 7635497415*X^4 + 61083979321*X^3 - 488671834567*X^2
    + 3909374676537*X - 31274997412295
  let A : ℤ[X] := 38321332409
  let G : ℤ[X] := X^12 + X^8 + X^6 + X^5 + X^3 + 1
  let Qp : ℤ[X] := 711*X^15 + 1552*X^14 + 1353*X^13 + 2945*X^12 + 3267*X^11 + 691*X^10 + 1712*X^9
    + 73*X^8 + 127*X^7 - 305*X^6 + 3151*X^5 + 1619*X^4 + 817*X^3 + 704*X^2 + 1608*X + 905
  let Rp : ℤ[X] := -711*X^11 - 841*X^10 + 199*X^9 - 1592*X^8 - 1033*X^7 + 1735*X^6 - 1533*X^5 - 1505*X^4
    - 1018*X^3 + 904*X^2 - 7232*X + 5624
  let QP : ℤ[X] := X^15 + 2*X^14 + 2*X^13 + 4*X^12 + 4*X^11 + X^10 + 2*X^9 + 4*X^5 + 2*X^4 + X^3 + X^2
    + 2*X + 1
  let RP : ℤ[X] := -X^11 - X^10 - 2*X^8 - X^7 + 2*X^6 - 2*X^5 - 2*X^4 - X^3 - 8*X + 7
  let C1 : ℤ[X] := X^11 - 8*X^10 + 64*X^9 - 512*X^8 + 4097*X^7 - 32776*X^6 + 262209*X^5 - 2097671*X^4
    + 16781368*X^3 - 134250943*X^2 + 1074007544*X - 8592060352
  let C2 : ℤ[X] := 10527873
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
theorem seventeenCertificate_6563 [Fact (Nat.Prime 6563)]
    (hpn : 6563 ≠ 17)
    (hmod : 6563 % 17 = 1) : SeventeenCertificate 6563 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 411
  let Q : ℤ[X] := X^15 - 410*X^14 + 168511*X^13 - 69258020*X^12 + 28465046221*X^11 - 11699133996830*X^10
    + 4808344072697131*X^9 - 1976229413878520840*X^8 + 812230289104072065241*X^7
    - 333826648821773618814050*X^6 + 137202752665748957332574551*X^5 - 56390331345622821463688140460*X^4
    + 23176426183050979621575825729061*X^3 - 9525511161233952624467664374644070*X^2
    + 3914985087267154528656210057978712771*X - 1609058870866800511277702333829250948880
  let A : ℤ[X] := 100765381064491087937701608898952024987
  let G : ℤ[X] := X^14 + X^12 + X^10 + X^9 + X^6 + X^5 + X^4 + X^2 + 1
  let Qp : ℤ[X] := 1659*X^15 + 2362*X^14 + 2201*X^13 + 2742*X^12 + 3533*X^11 + 19*X^10 + 413*X^9
    + 2554*X^8 + 2045*X^7 + 1228*X^6 + 2302*X^5 + 609*X^4 + 754*X^3 + 226*X^2 + 655*X + 1537
  let Rp : ℤ[X] := -1659*X^13 - 703*X^12 - 1498*X^11 - 1244*X^10 - 2289*X^9 + 611*X^8 - 1727*X^7
    + 993*X^6 - 2876*X^5 - 963*X^4 + 354*X^3 - 1108*X^2 - 5681*X + 5026
  let QP : ℤ[X] := 104*X^15 + 148*X^14 + 138*X^13 + 172*X^12 + 221*X^11 + X^10 + 26*X^9 + 160*X^8
    + 128*X^7 + 77*X^6 + 144*X^5 + 38*X^4 + 47*X^3 + 14*X^2 + 41*X + 96
  let RP : ℤ[X] := -104*X^13 - 44*X^12 - 94*X^11 - 78*X^10 - 143*X^9 + 38*X^8 - 108*X^7 + 62*X^6
    - 180*X^5 - 60*X^4 + 22*X^3 - 70*X^2 - 355*X + 315
  let C1 : ℤ[X] := X^13 - 411*X^12 + 168922*X^11 - 69426942*X^10 + 28534473163*X^9 - 11727668469992*X^8
    + 4820071741166712*X^7 - 1981049485619518632*X^6 + 814211338589622157753*X^5
    - 334640860160334706836482*X^4 + 137537393525897564509794103*X^3 - 56527868739143899013525376333*X^2
    + 23232954051788142494558929672864*X - 9548744115284926565263720095547104
  let C2 : ℤ[X] := 597978642599741706281180703835115
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
theorem seventeenCertificate_6733 [Fact (Nat.Prime 6733)]
    (hpn : 6733 ≠ 17)
    (hmod : 6733 % 17 = 1) : SeventeenCertificate 6733 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 912
  let Q : ℤ[X] := X^15 - 911*X^14 + 830833*X^13 - 757719695*X^12 + 691040361841*X^11
    - 630228809998991*X^10 + 574768674719079793*X^9 - 524189031343800771215*X^8
    + 478060396585546303348081*X^7 - 435991081686018228653449871*X^6
    + 397623866497648624531946282353*X^5 - 362632966245855545573135009505935*X^4
    + 330721265216220257562699128669412721*X^3 - 301617793877192874897181605346504401551*X^2
    + 275075428015999901906229624076012014214513*X - 250868790350591910538481417157322956963635855
  let A : ℤ[X] := 33980742135710652370577016552425150267464117
  let G : ℤ[X] := X^9 + X^8 + X^6 + X^2 - X
  let Qp : ℤ[X] := 4092*X^15 + 2270*X^14 + 883*X^13 + 23*X^12 + 3315*X^11 + 3929*X^10 + 2800*X^9
    + 2299*X^8 + 1367*X^7 + 2993*X^6 + 1341*X^5 - 227*X^4 + 2393*X^3 + 3168*X^2 + 3333*X + 979
  let Rp : ℤ[X] := -4092*X^8 - 2270*X^7 + 3209*X^6 - 1845*X^5 - 610*X^4 - 2519*X^3 + 1375*X^2 - 5754*X + 6733
  let QP : ℤ[X] := 554*X^15 + 307*X^14 + 119*X^13 + 3*X^12 + 449*X^11 + 532*X^10 + 379*X^9 + 311*X^8
    + 185*X^7 + 405*X^6 + 181*X^5 - 31*X^4 + 324*X^3 + 429*X^2 + 451*X + 132
  let RP : ℤ[X] := -554*X^8 - 307*X^7 + 435*X^6 - 250*X^5 - 83*X^4 - 341*X^3 + 186*X^2 - 779*X + 912
  let C1 : ℤ[X] := X^8 - 911*X^7 + 830832*X^6 - 757718783*X^5 + 691039530096*X^4 - 630228051447552*X^3
    + 574767982920167424*X^2 - 524188400423192690687*X + 478059821185951733906543
  let C2 : ℤ[X] := -64754278467486704488752
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
theorem seventeenCertificate_6869 [Fact (Nat.Prime 6869)]
    (hpn : 6869 ≠ 17)
    (hmod : 6869 % 17 = 1) : SeventeenCertificate 6869 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 982
  let Q : ℤ[X] := X^15 - 981*X^14 + 963343*X^13 - 946002825*X^12 + 928974774151*X^11
    - 912253228216281*X^10 + 895832670108387943*X^9 - 879707682046436960025*X^8
    + 863872943769601094744551*X^7 - 848323230781748275039149081*X^6
    + 833053412627676806088444397543*X^5 - 818058451200378623578852398387225*X^4
    + 803333399078771808354433055216254951*X^3 - 788873397895353915804053260222362361881*X^2
    + 774673676733237545319580301538359839367143*X - 760729550552039269503827856110669362258534425
  let A : ℤ[X] := 108754755953137656522457265206096566274258379
  let G : ℤ[X] := X^15 - X^14 - X^10 - X^9 + X^7 - X
  let Qp : ℤ[X] := -368*X^15 - 3049*X^14 - 1134*X^13 + 442*X^12 - 1665*X^11 - 160*X^10 - 1235*X^9
    - 3411*X^8 - 2838*X^7 - 2266*X^6 - 712*X^5 - 1822*X^4 - 3973*X^3 - 474*X^2 - 1992*X - 1889
  let Rp : ℤ[X] := 368*X^14 + 2313*X^13 - 4596*X^12 + 339*X^11 + 3683*X^10 - 3980*X^9 - 469*X^8
    + 335*X^7 + 1110*X^6 + 2151*X^5 - 3499*X^4 + 1518*X^3 - 103*X^2 - 8758*X + 6869
  let QP : ℤ[X] := -53*X^15 - 436*X^14 - 162*X^13 + 63*X^12 - 238*X^11 - 23*X^10 - 177*X^9 - 488*X^8
    - 406*X^7 - 324*X^6 - 102*X^5 - 261*X^4 - 568*X^3 - 68*X^2 - 285*X - 270
  let RP : ℤ[X] := 53*X^14 + 330*X^13 - 657*X^12 + 49*X^11 + 526*X^10 - 569*X^9 - 67*X^8 + 48*X^7
    + 159*X^6 + 307*X^5 - 500*X^4 + 217*X^3 - 16*X^2 - 1251*X + 982
  let C1 : ℤ[X] := X^14 - 983*X^13 + 965306*X^12 - 947930492*X^11 + 930867743144*X^10
    - 914112123767409*X^9 + 897658105539595637*X^8 - 881500259639882915534*X^7
    + 865633254966365023054389*X^6 - 850051856376970452639409998*X^5
    + 834750922962184984491900618036*X^4 - 819725406348865654771046406911352*X^3
    + 804970349034586072985167571586947664*X^2 - 790480882751963523671434555298382606048*X
    + 776252226862428180245348733303011719139135
  let C2 : ℤ[X] := -110973895294643248362342765483120906710530
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
theorem seventeenCertificate_6971 [Fact (Nat.Prime 6971)]
    (hpn : 6971 ≠ 17)
    (hmod : 6971 % 17 = 1) : SeventeenCertificate 6971 hpn := by
  dsimp only [SeventeenCertificate]
  let P : ℤ[X] := X + 800
  let Q : ℤ[X] := X^15 - 799*X^14 + 639201*X^13 - 511360799*X^12 + 409088639201*X^11
    - 327270911360799*X^10 + 261816729088639201*X^9 - 209453383270911360799*X^8
    + 167562706616729088639201*X^7 - 134050165293383270911360799*X^6
    + 107240132234706616729088639201*X^5 - 85792105787765293383270911360799*X^4
    + 68633684630212234706616729088639201*X^3 - 54906947704169787765293383270911360799*X^2
    + 43925558163335830212234706616729088639201*X - 35140446530668664169787765293383270911360799
  let A : ℤ[X] := 4032758173079175345837069607618220732906131
  let G : ℤ[X] := X^10 - X^7 - X^4 - X^2
  let Qp : ℤ[X] := -856*X^15 + 786*X^14 - 2266*X^13 - 516*X^12 + 655*X^11 - 2031*X^10 - 299*X^9
    + 1330*X^8 + 1707*X^7 - 140*X^6 - 392*X^5 - 951*X^4 + 105*X^3 - 1204*X^2 + 346*X + 1184
  let Rp : ℤ[X] := 856*X^9 - 1642*X^8 + 3052*X^7 - 2606*X^6 + 471*X^5 - 366*X^4 - 838*X^3 + 1184*X^2
    - 6971*X + 6971
  let QP : ℤ[X] := -98*X^15 + 90*X^14 - 260*X^13 - 59*X^12 + 75*X^11 - 233*X^10 - 34*X^9 + 153*X^8
    + 196*X^7 - 16*X^6 - 45*X^5 - 109*X^4 + 12*X^3 - 138*X^2 + 40*X + 136
  let RP : ℤ[X] := 98*X^9 - 188*X^8 + 350*X^7 - 299*X^6 + 54*X^5 - 42*X^4 - 96*X^3 + 135*X^2 - 799*X + 800
  let C1 : ℤ[X] := X^9 - 800*X^8 + 640000*X^7 - 512000001*X^6 + 409600000800*X^5 - 327680000640000*X^4
    + 262144000511999999*X^3 - 209715200409599999200*X^2 + 167772160327679999359999*X
    - 134217728262143999487999200
  let C2 : ℤ[X] := 15402981295325663404160000
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
