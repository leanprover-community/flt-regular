import ring_theory.class_group

def nat.prime.regular (p : ℕ) [fact p.prime] : Prop := sorry

theorem flt_regular (p a b c : ℕ) [fact p.prime] (h : a ^ p + b ^ p = c ^ p) :
  a * b * c = 0 := sorry