import data.nat.totient
import algebra.char_p.two

namespace nat

-- combinatorial arguments would be more annoying than this
lemma totient_even {n : ℕ} (hn : 2 < n) : even n.totient :=
begin
  haveI : fact (0 < n) := ⟨pos_of_gt hn⟩,
  haveI : fact (1 < n) := ⟨one_lt_two.trans hn⟩,
  have : 2 = order_of (-1 : (zmod n)ˣ), by rw [←order_of_units, units.coe_neg_one, order_of_neg_one,
                                       ← @ring_char.eq (zmod n) _ n (zmod.char_p n), if_neg hn.ne'],
  rw [← zmod.card_units_eq_totient, even_iff_two_dvd, this],
  exact order_of_dvd_card_univ
end

end nat
