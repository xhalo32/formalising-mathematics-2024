/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the tactics

/-!

# Challenge sheet

This is a harder group theory question.

It turns out that two of the axioms in the standard definition of a group
are not needed; they can be deduced from the others. Let's define
a "weak group" class, where we only have three of the group axioms.
The question is: can you prove that a weak group is a group, by
proving the other axioms?

-/

namespace Section5sheet2


-- removing `mul_one` and `mul_inv_self` from the five standard axioms
-- for a group.
class WeakGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

namespace WeakGroup

-- Let `G` be a "weak group" and say a,b,c are in G
variable {G : Type} [WeakGroup G] (a b c : G)

/-

The (tricky) challenge is to prove that G is a group, which we can interpret as
proving the missing axioms `mul_one` and `mul_inv_self`. Note that you
can't use the `group` tactic any more because `G` isn't a group yet:
this is what you're trying to prove!

One way of doing it: try proving

`mul_left_cancel : a * b = a * c → b = c`

and then

`mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c`

first.

-/

theorem mul_left_cancel (h : a * b = a * c) : b = c := by
  calc b = a⁻¹ * a * b := by rw [inv_mul_self, one_mul]
  _ = a⁻¹ * a * c := by simp only [mul_assoc, h]
  _ = c := by rw [inv_mul_self, one_mul]

theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  calc a * b = a * a⁻¹ * c := by rw [h, mul_assoc]
  _ = a⁻¹⁻¹ * a⁻¹ * a * a⁻¹ * c := by simp only [inv_mul_self, one_mul]
  _ = a⁻¹⁻¹ * (a⁻¹ * c) := by simp only [mul_assoc, inv_mul_self a, one_mul]
  _ = c := by simp only [← mul_assoc, inv_mul_self, one_mul]

-- Pretty much copy the simp lemmas from above
theorem mul_one (a : G) : a * 1 = a := by
  calc a * 1 = a * a⁻¹ * a := by simp only [mul_assoc, inv_mul_self, one_mul]
  _ = a⁻¹⁻¹ * a⁻¹ * a * a⁻¹ * a := by simp only [← mul_assoc, inv_mul_self, one_mul]
  _ = a⁻¹⁻¹ * a⁻¹ * a := by simp only [mul_assoc, inv_mul_self a, one_mul]
  _ = a := by simp only [← mul_assoc, inv_mul_self, one_mul]

-- Again copy-pasted the same thing and tweaked it a bit
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  calc a * a⁻¹ = a⁻¹⁻¹ * a⁻¹ * a * a⁻¹ := by simp only [← mul_assoc, inv_mul_self, one_mul]
  _ = a⁻¹⁻¹ * a⁻¹ := by simp only [mul_assoc, inv_mul_self a, one_mul]
  _ = 1 := by simp only [← mul_assoc, inv_mul_self, one_mul]

end WeakGroup

/-

If you want to take this further: prove that if we make
a new class `BadGroup` by replacing
`one_mul` by `mul_one` in the definition of `weak_group`
then it is no longer true that you can prove `mul_inv_self`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_self` but which really are not groups.
Can you find an example? Try it on paper first.

-/
-- claim: not a group in general
class BadGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

-- `Bool` is a type with two terms, `Bool.true` and `Bool.false`. See if you can make it into
-- a bad group which isn't a group!
instance : One Bool :=
  ⟨true⟩

instance : Mul Bool :=
  ⟨fun a b => a⟩

instance : Inv Bool :=
  ⟨fun a => true⟩

instance : BadGroup Bool where
  mul_assoc := by
    intros
    rfl
  -- `decide`, might be able to do this
  mul_one := by
    intro
    rfl
  inv_mul_self := by
    intro a
    rfl

example : ¬∀ a : Bool, 1 * a = a := by
  intro h
  specialize h false
  cases h
  -- decide
