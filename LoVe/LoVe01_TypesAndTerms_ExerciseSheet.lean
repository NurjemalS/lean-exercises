import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.
 -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun f b a ↦ f a b

def projFst : α → α → α :=
  fun a b ↦ a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun a b ↦ b

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun f x h y ↦ h x



/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. Start with an empty context. You might find the
characters `–` (to draw horizontal bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

end LoVe
