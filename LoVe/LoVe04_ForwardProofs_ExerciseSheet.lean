/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
  assume ha : a
  show a from
    ha
  
theorem K (a b : Prop) :
    a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume h : a → b → c
  assume hb : b
  assume ha : a
  show c from
    h ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from
    ha1

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  assume ha1 : a
  assume ha2 : a
  show a from
    ha1

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  assume h1 : a → b → c
  assume ha : a
  assume h2 : a → c
  assume hb : b
  show c from
    h1 ha hb

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : ¬ b
  assume ha : a
  show False from
    hnb (hab ha)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (assume h : ∀x, p x ∧ q x
     show (∀x, p x) ∧ (∀x, q x) from
       And.intro
         (assume x : α
          show p x from
            And.left (h x))
         (assume x : α
          show q x from
            And.right (h x)))
    (assume h : (∀x, p x) ∧ (∀x, q x)
     show ∀x, p x ∧ q x from
       fix x : α
       have hp : p x :=
         And.left h x
       have hq : q x :=
         And.right h x
       show p x ∧ q x from
         And.intro hp hq)

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume h : ∃x, ∀y, p x y
  show ∀y, ∃x, p x y from
    Exists.elim h
      (fix x : α
       assume hx : ∀y, p x y
       show ∀y, ∃x', p x' y from
         fix y : α
         show ∃x', p x' y from
           Exists.intro x (hx y))


/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
 calc
    (a + b) * (a + b)
        = a * (a + b) + b * (a + b) := by
            -- (a + b) * (a + b) = a*(a + b) + b*(a + b)
            simpa using add_mul a b (a + b)
    _   = (a * a + a * b) + (b * a + b * b) := by
            -- distribute a and b over (a + b)
            simp [mul_add, add_comm, add_left_comm, add_assoc]
    _   = a * a + a * b + b * a + b * b := by
            -- regroup additions
            ac_rfl
    _   = a * a + a * b + a * b + b * b := by
            -- commutativity of multiplication: b * a = a * b
            have h : b * a = a * b := by ac_rfl
            simp [h]
    _   = a * a + (a * b + a * b) + b * b := by
            -- regroup so the two a*b are next to each other
            ac_rfl
    _   = a * a + 2 * (a * b) + b * b := by
            -- 2 * (a * b) = a * b + a * b
            simp [Nat.two_mul, add_comm, add_left_comm, add_assoc]
    _   = a * a + 2 * a * b + b * b := by
            -- 2 * (a * b) = 2 * a * b by associativity/commutativity
            ac_rfl

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  sorry


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
    False :=
  have h : (∀x : Bool, x = true ∧ True) ↔ True :=
    All.one_point_wrong (α := Bool) true (fun _ => True)
  have hall : ∀x : Bool, x = true ∧ True :=
    Iff.mpr h True.intro
  have hfalse : false = true :=
    And.left (hall false)
  show False from
    by cases hfalse

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False :=
  sorry

end LoVe
