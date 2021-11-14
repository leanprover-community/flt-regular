import data.finsupp.basic
import tactic.slim_check

namespace slim_check
namespace total_function
section
universes u v w
variables {α : Type u} {β : Type v} {γ : Sort w}

variables [sampleable α] [sampleable β]

variables [decidable_eq α] [decidable_eq β]

variables [has_repr α] [has_repr β] [has_zero β]

/-- Map a total_function to one whose default value is zero so that it represents a finsupp. -/
@[simp]
def zero_default : total_function α β →
                   total_function α β
| (with_default A y) := with_default A 0
/-- The suppport of a zero default `total_function`. -/
@[simp]
def zero_default_supp : total_function α β → finset α
| (with_default A y) :=
  list.to_finset $ (A.erase_dupkeys.filter (λ ab, sigma.snd ab ≠ 0)).map sigma.fst

def apply_finsupp (tf : total_function α β) : α →₀ β :=
{ support := zero_default_supp tf,
  to_fun := tf.zero_default.apply,
  mem_support_to_fun := begin
    intro a,
    rcases tf with ⟨A, y⟩,
    simp [apply],
    split,
    { rintro ⟨od, hval, hod⟩,
      have := list.mem_lookup _ hval,
      rw (_ : list.lookup a A = od),
      simpa,
      rw list.lookup_erase_dupkeys at this,
      finish,
      exact list.nodupkeys_erase_dupkeys A, },
    { intro h,
      existsi (A.lookup a).get_or_else (0 : β),

      rw ← list.lookup_erase_dupkeys at h ⊢,
      simp [h, ← list.mem_lookup_iff (A.nodupkeys_erase_dupkeys)],
      cases list.lookup a A.erase_dupkeys,
      { simpa using h, },
      { simp, }, }
  end }
instance finsupp.sampleable_ext : sampleable_ext (α →₀ β) :=
{ proxy_repr := total_function α β,
  interp := total_function.apply_finsupp,
  sample := do {
    xs ← (sampleable.sample (list (α × β)) : gen ((list (α × β)))),
    ⟨x⟩ ← (uliftable.up $ sample β : gen (ulift.{max u v} β)),
    pure $ total_function.with_default (list.to_finmap' xs) x },
  shrink := total_function.shrink }
  end
end total_function
end slim_check
lemma all_finsupp_eq_zero (f : ℕ →₀ ℕ) : f = 0 :=
begin
  slim_check, --outputs a counterexample
  success_if_fail {slim_check,},
  sorry,
end
