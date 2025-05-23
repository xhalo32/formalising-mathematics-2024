/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Data.Polynomial.FieldDivision
-- polynomial rings over a field are EDs

/-

# Euclidean Domains

Lean's definition of a Euclidean domain is more general than the usual one presented
to undergraduates. First things first: here's how to say "let R be a Euclidean domain"

-/

section Section14Sheet2

variable (R : Type) [EuclideanDomain R]

/-

And there's various theorems (all known by the typeclass inference system) about
Euclidean domains:

-/

example : EuclideanDomain ℤ := by infer_instance

open scoped Polynomial

-- I neither know nor care why it's noncomputable, but it doesn't matter to mathematicians
noncomputable example (k : Type) [Field k] : EuclideanDomain k[X] :=
  inferInstance

-- Euclidean domains are PIDs
example (R : Type) [EuclideanDomain R] : IsPrincipalIdealRing R :=
  inferInstance

example (R : Type) [EuclideanDomain R] : IsDomain R :=
  inferInstance

/-

Internally the definition of a Euclidean domain is this. It's a ring with the following
structure/axioms:

1) You have a "quotient" function `quotient r s` and a remainder function `remainder r s`,
both of type `R → R → R` (i.e. functions from `R²` to `R`)

2) You have an axiom saying `∀ a b, a = b * quotient a b + remainder a b`

3) You have a binary relation `≺` on the ring such that `remainder a b ≺ b`

4) You have an axiom saying that `≺` is well-founded, i.e., there are no infinite decreasing
sequences.

The point is that these axioms are enough to get Euclid's algorithm to work.

In usual maths you have a function from `R` to `ℕ` sending an element `b` to its "size",
and an axiom saying that the remainder when you divide something by `b` is sent to a smaller
natural number. In Lean the natural numbers are not involved; all that we guarantee is
that you can't keep taking remainders infinitely often, which turns out to be a very slightly
weaker statement. Let's prove that any "normal" Euclidean domain is a mathlib Euclidean domain.

-/
open Classical

theorem acc_of_is_minimal {α} {r : α → α → Prop} (x : α)
  (h : ∀ y, ¬ r y x) : Acc r x := Acc.intro x (λ y r_yx => absurd r_yx (h y))

noncomputable example (R : Type) [CommRing R] [IsDomain R] (φ : R → ℕ)
    (h : ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ φ r < φ b))
    (h0 : ∀ a b : R, a ≠ 0 → b ≠ 0 → φ a ≤ φ (a * b)) :
    EuclideanDomain R := by
  let φ' : R → ℕ := fun r => if r = 0 then 0 else 1 + φ r
  have h' (a b : R) : ∃ q r : R,
    a = b * q + r ∧ (b = 0 ∧ q = 0 ∧ r = a ∨ b ≠ 0 ∧ φ' r < φ' b)
  ·
    have h' := h a b
    have h0' := h0 a b
    by_cases hb : b = 0
    · refine ⟨0, a, ?_⟩
      constructor
      · norm_num
      · left
        tauto
    · specialize h' hb
      obtain ⟨q, r, h1, h2⟩ := h'
      refine ⟨q, r, h1, ?_⟩
      right
      refine ⟨hb, ?_⟩
      cases' h2 with h2 h2
      · simp [h2]
        split
        · contradiction
        · linarith
      · simp [hb]
        split
        · linarith
        · linarith [h2]

  choose quot rem h'' using h'
  exact
    { quotient := quot
      quotient_zero := by
        intro a
        specialize h'' a 0
        tauto
      remainder := rem
      quotient_mul_add_remainder_eq := by
        intro a b
        specialize h'' a b
        tauto
      r := fun a b => φ' a < φ' b
      r_wellFounded := by
        refine WellFounded.onFun (f := φ') wellFounded_lt -- apply? found this immediately
        -- have := measure φ'
        -- constructor
        -- intro a

        -- have : Acc (fun a b ↦ φ' a < φ' b) 0
        -- · apply acc_of_is_minimal
        --   simp -- nothing is less than φ' 0 = 0


        -- -- constructor
        -- -- intro b bh
        -- -- constructor
        -- -- intro c ch
        -- -- Doing this process repeatedly gets a decreasing chain φ' c < φ' b < φ' a, which must eventually lead to φ' z < 0, a contradiction

        -- have := @Set.WellFoundedOn.acc_iff_wellFoundedOn R (fun a b ↦ φ' a < φ' b) a
        -- have := this.out 0 2
        -- rw [this]



        -- constructor
        -- intro b
        -- obtain ⟨b, bh⟩ := b
        -- rw [Set.mem_setOf] at bh
        -- rw [@Relation.transGen_iff] at bh
        -- cases bh
        -- case _ h =>
        --   obtain ⟨eq, h2⟩ := h'' b a
        --   cases' h2 with h2 h2
        --   · rw [h2.1] at h
        --     simp at h -- φ' 0 = 0
        --   · -- a ≠ 0 therefore quot b a = 0
        --     sorry
        -- -- have := WellFounded.induction wellFounded_lt 0

      remainder_lt := by
        intro a b hab
        specialize h'' a b
        tauto
      mul_left_not_lt := by
        intro a b hb
        push_neg
        -- I know h0 is already a part of h'', but it's just faster to use here
        by_cases ha : a = 0
        · simp [ha]
        ·
          specialize h0 a b ha hb
          simp [ha, hb]
          exact h0
    }

#check Acc

-- inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
-- | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x

end Section14Sheet2
