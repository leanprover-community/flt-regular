import algebra.big_operators.basic
import data.nat.totient
import tactic.ring_exp
import algebra.gcd_monoid.basic
import data.nat.mul_ind

open finset
open_locale big_operators

variables {A : Type*} [has_mul A] {B : Type*} [has_mul B] [has_le B]


namespace function

/-- We say that a function `f` is `super_multipicative` if
  `∀ (a b : A), f (a) * f(b) ≤ f(a * b)`. -/
def super_multiplicative (f : A → B) : Prop := ∀ (a b : A), f (a) * f(b) ≤ f(a * b)

end function

namespace nat

open nat

localized "notation `φ` := nat.totient" in nat

lemma gcd_self_pow (p n m : ℕ) : (p ^ n).gcd (p ^ m) = p ^ (min n m) :=
begin
  wlog h : n ≤ m,
  rw [min_eq_left h],
  apply gcd_eq_left,
  exact pow_dvd_pow p h,
end

lemma totient_pow_mul_self {p n m : ℕ} (h : prime p)  :
   φ ((p ^ n).gcd (p ^ m)) * φ (p ^ n * p ^ m) = φ (p ^ n) * φ (p ^ m) * (p ^ n).gcd (p ^ m) :=
begin
  --wlog hnm : n ≤ m using [n m], -- chris: this is a nice tactic you'll be interested in!
  have hnm : n ≤ m, sorry,
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp only [gcd_one_left, mul_one, one_mul, pow_zero]},
  rcases m.eq_zero_or_pos with rfl | hm,
  { simp only [mul_one, one_mul, gcd_one_right, totient_one, pow_zero]},
  have h20 : 0 < n + m, by linarith,
  rw [totient_prime_pow h hn, totient_prime_pow h hm, ←pow_add, totient_prime_pow h h20,
      gcd_self_pow, min_eq_left hnm, totient_prime_pow h hn, ← mul_assoc],
  /- temporarily sorrying the change and the wlog, as they're super slow!
  ac_change p ^ (n - 1) * ((p - 1) * ((p - 1) * p ^ (n + m - 1))) =
            p ^ (n - 1) * ((p - 1) * ((p - 1) * (p ^ (m - 1) * p ^ n))), -/
  suffices : p ^ (n - 1) * ((p - 1) * ((p - 1) * p ^ (n + m - 1))) =
              p ^ (n - 1) * ((p - 1) * ((p - 1) * (p ^ (m - 1) * p ^ n))), sorry,
  rw ←pow_add,
  congr,
  linarith
end

--This is a made-up name, I just wanted to call it something ~Chris
/-- We say that a function `f` satisfies `is_gcd_mult` if
  `∀ (a b: ℕ), f (a.gcd b) * f (a * b) = f a * f b * (a.gcd b)`. -/
def is_gcd_mult (f : ℕ → ℕ) : Prop :=
  ∀ a b: ℕ, f (a.gcd b) * f (a * b) = f a * f b * (a.gcd b)

lemma totient_mul_gen : is_gcd_mult φ :=
begin
  intro a,
  rcases a.eq_zero_or_pos with rfl | ha,
  { simp },
  apply nat.rec_on_prime_coprime,
  { simp only [zero_mul, mul_zero, totient_zero] },
  { intros p n hp,
    rcases n.eq_zero_or_pos with rfl | hn,
    { simp only [mul_one, one_mul, gcd_one_right, totient_one, pow_zero] },
    rcases coprime_or_dvd_of_prime hp a,
    { -- p.coprime a
      have key : a.gcd (p ^ n) = 1 := (coprime.pow_right n h.symm).gcd_eq_one,
      simpa only [key, mul_one, one_mul, totient_one] using totient_mul key },
    { -- p ∣ a
      induction a using nat.rec_on_prime_coprime,
      { simp only [zero_mul, mul_zero, totient_zero] },
      case hp : q m hq
      { have := (prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h),
        subst this,
        exact totient_pow_mul_self hp },
      case h : a b hab ha hb
      { rw hp.dvd_mul at h,
        cases h,
        rw mul_comm at ha,
        all_goals { sorry }
      } } },
  intros c d hcd hc hd,
  rw [coprime.gcd_mul _ hcd, totient_mul hcd],
  apply (mul_right_inj' (totient_pos ha).ne').mp,
  ac_change _ = (a.totient * d.totient * a.gcd d) * (a.totient * c.totient * a.gcd c),
  rw [←hc, ←hd],
  -- we'd like wlog a divides one (or they're all coprime)
  have : ((a.coprime c) ∧ (a.coprime d)) ∨ (¬a.coprime c ∨ ¬a.coprime d), by tauto,
  rcases this with ⟨hac, had⟩ | hacd,
  { sorry },
  sorry
end

lemma totient_is_super_multiplicative :  function.super_multiplicative φ :=
begin
  intros a b,
  let d := a.gcd b,
  by_cases d ≠ 0,
  {have := totient_mul_gen a b,
  simp at *,
  have hd: 0 < d.totient,  by {apply totient_pos, exact pos_iff_ne_zero.mpr h, },
  by_cases HA : a ≠ 0,
  by_cases HB : b ≠ 0,
  have ha: 0 < a.totient,
    by {apply totient_pos, by_contra H, simp at *, rw H at HA, simp at HA, exact HA,},
  have hb: 0 < b.totient,
    by {apply totient_pos, by_contra H, simp at *, rw H at HB, simp at HB, exact HB},
  have hdd: φ( d ) ≤ d, by {apply totient_le,},
  have hr :  φ (d) * (φ (a) * φ (b)) ≤ φ (d) * φ (a * b) ↔ (φ (a) * φ (b)) ≤ φ (a * b) ,
  by {apply mul_le_mul_left hd,},
  simp_rw ← hr,
  rw this,
  rw mul_comm,
  exact mul_le_mul_left' hdd (φ a * φ b),
  simp at HB,
  rw HB,
  simp,
  simp at HA,
  rw HA,
  simp,
  },
  simp at h,
  simp_rw d at h,
  rw gcd_eq_zero_iff at h,
  simp [h.1],
end



theorem mul_ind {P : ℕ → ℕ → Prop}
  (H0 : ∀ (n : ℕ), P 0 n)
  (H1 : ∀ (n : ℕ), P 1 n)
  (Hc : ∀ (x y z w : ℕ), (w.coprime y) → (x.coprime z)  →  P w x → P y z → (w*y).coprime (x*z) →  P (w*y)  (x*z))
  (Hp : ∀ (p n m: ℕ), (prime p) →  P (p^n) (p^m)) :
  ∀ n m,   P n m :=
begin
let Pl:= λ n, P n 1,
let Pr:= λ m, P 1 m,

have h1: ∀ n, Pl n, by {sorry,},
have h2: ∀ m, Pr m, by {sorry,},
intros n m,
have hc:= Hc 1 1 m n,
simp at hc,
simp_rw Pl at h1,
simp_rw Pr at h2,
apply hc (h1 n) (h2 m),
sorry
end

-- this is atrocious!
lemma gcd_mul_fun (x y w z : ℕ) (hzy : z.coprime y) (hxw: x.coprime w) :
  (z*y).gcd (x*w)= (z.gcd x)*(y.gcd w)*(z.gcd w)*(y.gcd x) :=
begin
rw coprime.gcd_mul (z*y) hxw,
simp_rw gcd_comm,
rw coprime.gcd_mul x hzy,
rw coprime.gcd_mul w hzy,
rw ← mul_assoc,
ac_refl,
end

lemma totient_mul_gen' : is_gcd_mult φ :=

begin


apply mul_ind,
simp,
simp,
intros x y w z hzy hxw hpwx hpyz,


sorry,

intros p n m hp,
apply totient_pow_mul_self p n m hp,

/-
  rw is_gcd_mult,
  intros a b,
 by_cases a.coprime b ,
 rw coprime at h,
 rw h,
 simp [totient_mul h],

 have hd : 0 < a.gcd b, by {sorry,},
 have := exists_coprime hd,
 obtain ⟨n,m, hnm, hn, hm⟩ := this,
 rw [hn, hm],
 simp [← mul_assoc],
 by_cases hnd: n.coprime (a.gcd b),
 by_cases hmd: m.coprime (a.gcd b),
 rw totient_mul hnd,
rw totient_mul hmd,
have eq1: ( n*d*m*d = (n* m) * d^2), by {sorry,},
rw eq1,
have hnmd: (n*m).coprime (d^2), by {sorry,},
rw totient_mul hnmd,
rw totient_mul hnm,
simp_rw ← mul_assoc,
have HH := totient_mul_self d,

--rw totient_mul hnd,
-/
end


lemma prime_extraction {m n : ℕ} (h : ¬ n.coprime m) :
  ∃ (kn km p n' m': ℕ), p.prime ∧ coprime (p^(kn+km)) (n'*m') ∧ coprime (p^kn) (n') ∧
  coprime (p^km) (m') ∧ n=p^kn*n' ∧ m = p^(km)*m' ∧ n' < n ∧ m' < m :=
begin
sorry,
end

/-- We say that a function `f` satisfies `is_gcd_mult'` if
  `∀ a b : ℕ, f (a * b) = (f a * f b * a.gcd b) / f (a.gcd b)`. -/
def is_gcd_mult' (f : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, f (a * b) = (f a * f b * (a.gcd b)) / f (a.gcd b)

--How do you do double strong induction???
lemma tot_mul_gen : is_gcd_mult' φ :=
begin
rw is_gcd_mult',
intros a b,
 apply nat.strong_induction_on a,
 intros aa haa,
 revert haa,
 apply nat.strong_rec_on b,
 intros bb hbb hg,
 by_cases aa.coprime bb ,
 rw coprime at h,
 rw h,
 simp [totient_mul h],
 have H:= prime_extraction h,
 obtain ⟨ka,kb,p,n',m',hp,hc,hn, hm, hhn, hhm, hind1, hind2⟩ := H,
 have hab: aa*bb=p^(ka+kb)*(n'*m'), by {sorry,},
 rw [hab, hhn],
 have HH:= hbb m' hind2,
sorry,

end


end nat
