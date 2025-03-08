/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    triv
  isOpen_inter := by
    -- let s and t be two sets
    intro s t
    -- assume they're open
    intro hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    triv
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    triv

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
    dsimp
    right
    rfl
  isOpen_inter := by
    dsimp
    intros s t hs ts
    cases' hs <;> subst s
    · cases' ts <;> subst t <;> left <;> apply Set.empty_inter
    · cases' ts <;> subst t
      · left
        apply Set.inter_empty
      · right
        apply Set.inter_self

  isOpen_sUnion := by
    intro F
    -- do cases on whether Set.univ ∈ F
    intro h
    dsimp at h
    by_cases hf : Set.univ ∈ F
    · right
      have gona := h _ hf
      cases' gona with h1
      · ext x
        constructor
        · intro xF
          apply Set.mem_univ
        · intro h2
          rw [h1] at h2
          exfalso
          apply Set.not_mem_empty x h2
      · ext x
        constructor
        · intro xF
          apply Set.mem_univ
        · intro h2
          rw [Set.mem_sUnion]
          use Set.univ
    · left
      ext x
      constructor
      · intro xF
        rw [Set.mem_sUnion] at xF
        cases' xF with s sh
        cases' sh with sF xs
        have : s = ∅
        · by_contra
          have gona := h _ sF
          cases' gona
          · contradiction
          · subst s
            contradiction
        subst s
        assumption
      · intro h1
        exfalso
        apply Set.not_mem_empty x h1

-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  -- have s : Set (Set X) := ∅
  rw [← Set.sUnion_empty]
  apply isOpen_sUnion
  intro t th
  contradiction

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  intro x _xh
  use 1
  constructor
  · exact Real.zero_lt_one
  · intro y _h
    -- exact _xh -- WTF
    exact Set.mem_univ _

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x h
  cases' h with xs xt
  · apply hs at xs
    apply ht at xt
    cases' xs with δs δsh
    cases' xt with δt δth
    use min δs δt
    constructor
    · exact lt_min δsh.1 δth.1
    · intro y
      intro h
      cases' h with hl hr
      constructor
      · apply δsh.2
        have h2 : δs ≥ min δs δt := by exact min_le_left δs δt
        constructor
        · calc x - δs ≤ x - min δs δt := by exact sub_le_sub_left h2 x
               _      < y             := by exact hl
        · calc y < x + min δs δt       := by exact hr
               _ ≤ x + δs             := by exact add_le_add_left h2 x
      · apply δth.2
        have h2 : δt ≥ min δs δt := by exact min_le_right δs δt
        constructor
        · calc x - δt ≤ _ := by exact sub_le_sub_left h2 x
              _       < y := by exact hl
        · calc y < _                  := by exact hr
               _ ≤ x + δt             := by exact add_le_add_left h2 x

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x xh
  rw [Set.mem_sUnion] at xh
  cases' xh with s sh
  cases' sh with sf xs
  have gona := hF _ sf
  cases' gona _ xs with δ h
  cases' h with δh ho
  use δ
  constructor
  · assumption
  · intro y h
    cases' h with hl hr
    rw [Set.mem_sUnion]
    use s
    constructor
    · assumption
    · apply ho
      constructor
      repeat assumption

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
