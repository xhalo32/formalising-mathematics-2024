/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Groups

## How to use Lean's groups

In previous courses I have made groups from scratch, but it's kind of irritating
to do (because all the lemma names like `mul_one` are already taken) and I'm
not entirely sure that most students want to know how to make their own
groups, rings, whatever: what's the point if these things are there already?

So in this sheet I explain how to use Lean's groups.

-/

-- let G be a group
variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
/-  Let's see what just happened.
    The tactic state now looks like this:

    G : Type
    inst✝ : Group G
    g : G
    ⊢ g⁻¹ * g = 1

    So G is what most mathematicians would call a "set", and what in this course
    we call a "type" (they're the same thing as far as you're concerned), and
    `g : G` just mean "g is an element of G". The remaining thing is this
    `inst✝` thing, and that means "G has a multiplication `*`, an identity `1`,
    an inverse function `⁻¹`, and satisfies all the group axioms; furthermore
    all of this will be taken care of by "instances", which are a part
    of Lean's "type class inference system". The type class inference system
    is the system which deals with stuff in square brackets. You don't have
    to worry about it right now -- all that matters is that you have access
    to all the group axioms. This one is called `inv_mul_self g`.
-/
  inv_mul_self g

-- Why don't you use `exact?` to see the names of the other axioms
-- of a group? Note that when `exact?` has run, you can click on
-- the output (the blue output in the infoview) and replace `exact?`
-- with the name of the axiom it found. Note also that you can instead *guess*
-- the names of the axioms. For example what do you think the proof of `1 * a = a` is called?
example (a b c : G) : a * b * c = a * (b * c) := by
  rw [mul_assoc]

-- can be found with `library_search` if you didn't know the answer already
example (a : G) : a * 1 = a := by
  rw [mul_one]

-- Can you guess the last two?
example (a : G) : 1 * a = a := by
  rw [one_mul]

example (a : G) : a * a⁻¹ = 1 := by
  rw [mul_inv_self]

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.
-- let a,b,c be elements of G in the below.
variable (a b c : G)

/-
Group class hierarchy:
`Group`: Just a `DivInvMonoid` with `mul_left_inv`
\- `DivInvMonoid`: Combines these three with compatibility requirements such as `div_eq_mul_inv` and `zpow_zero`
   |- `Div`: `/` notation
   |- `Inv`: Every element has an inverse. `⁻¹` notation
   \- `Monoid`: Combines these two with compatibility such as `pow_zero`
       |- `Semigroup`: Provides `mul_assoc`
          \- `Mul`: `*` notation
       \- `MulOneClass`: Provides `one_mul` and `mul_one`
          |- `One`: there is always a neutral `1` element
          \- `Mul`

The group axioms are as follows:
1. The operation `*` is associative and has a neutral element `1`.
2. For all elements `a`, there exists an inverse `a⁻¹` such that `a⁻¹ * a = 1`.
-/

#check mul_assoc -- `*` is associative
#check One.one -- neutral element `1`
#check one_mul
#check mul_one
#check mul_left_inv

-- Here are some of the compatibility requirements:
#check div_eq_mul_inv
#check zpow_zero
#check pow_zero

example : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, mul_left_inv, one_mul]

lemma example1 : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc]
  nth_rw 1 [← one_mul a]
  rw [← mul_left_inv a⁻¹, mul_assoc a⁻¹⁻¹, mul_left_inv, mul_one, mul_left_inv, one_mul]

example (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  -- hint for this one if you're doing it from first principles: `b * (a * c) = (b * a) * c`
  apply congrArg (. * c) at h1
  apply congrArg (b * .) at h2
  rw [one_mul] at h1
  rw [← mul_assoc, mul_one] at h2
  exact Eq.trans h2.symm h1

lemma example3 : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  · intro h
    calc a⁻¹ = a⁻¹ * 1      := by rw [mul_one]
          _ = a⁻¹ * a * b  := by rw [← h, mul_assoc]
          _ = 1 * b         := by rw [mul_left_inv]
          _ = b             := by rw [one_mul]
  · intro h
    calc a * b = a * a⁻¹                := by rw [h]
             _ = 1 * a * a⁻¹            := by rw [one_mul]
             _ = a⁻¹⁻¹ * a⁻¹ * a * a⁻¹     := by rw [mul_left_inv]
             _ = a⁻¹⁻¹ * 1 * a⁻¹          := by rw [mul_assoc a⁻¹⁻¹, mul_left_inv]
             _ = a⁻¹⁻¹ * a⁻¹              := by rw [mul_one]
             _ = 1                      := by rw [mul_left_inv]

example : (1 : G)⁻¹ = 1 := by
  nth_rw 2 [← mul_left_inv 1]
  rw [mul_one]

lemma example5 : a⁻¹⁻¹ = a := by
  nth_rw 2 [← one_mul a]
  rw [← mul_left_inv a⁻¹]
  rw [mul_assoc, mul_left_inv, mul_one]

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← example3]
  rw [mul_assoc, example1]
  nth_rw 1 [← example5 (a := a)]
  rw [mul_left_inv]

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `exact?` or by
educated guessing).

-/
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  intro g f
  calc g * f = g * f * 1 := by rw [mul_one]
  _ = g * f * f⁻¹ * f⁻¹  := by rw [← h f⁻¹, ← mul_assoc]
  _ = g * f⁻¹  := by rw [mul_assoc g, mul_right_inv, mul_one]
  _ = 1 * g * f⁻¹  := by rw [one_mul]
  _ = g⁻¹ * g⁻¹ * g * f⁻¹  := by rw [← h g⁻¹]
  _ = g⁻¹ * f⁻¹  := by rw [mul_assoc g⁻¹, mul_left_inv, mul_one]
  _ = g⁻¹ * f⁻¹ * 1 := by rw [mul_one]
  _ = g⁻¹ * f⁻¹ * (f * g) * (f * g) := by rw [← h (f * g), ← mul_assoc]
  _ = g⁻¹ * (f⁻¹ * f) * g * (f * g) := by simp only [mul_assoc]
  _ = f * g  := by simp only [mul_left_inv, mul_one, one_mul]
