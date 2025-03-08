/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question.

-/


lemma lemma1 {L : Type} [Lattice L] (a b c : L) : a ⊓ (b ⊔ c) ≤ (a ⊔ c) ⊓ (b ⊔ c) := by
  have h : a ≤ a ⊔ c := by exact le_sup_left
  simp only [le_inf_iff, inf_le_right, and_true, ge_iff_le]
  apply le_trans' h
  exact inf_le_left

lemma lemma2 {L : Type} [Lattice L] (a b c : L) : c ⊓ a ⊔ c ⊓ b ≤ a ⊔ b ⊓ c := by
  have ha : c ⊓ a ≤ a := by exact inf_le_right
  simp
  constructor
  · apply le_trans ha
    exact le_sup_left
  · apply le_sup_of_le_right
    rw [inf_comm]

example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor
  ·
    intro h a b c
    obtain ⟨h1, h2⟩ := le_antisymm_iff.mp (h (a ⊓ b) a c)
    apply le_antisymm
    · apply le_trans' h2
      simp only [ge_iff_le, inf_le_left, sup_of_le_right, le_inf_iff, true_and]
      -- changes lhs to (a ⊔ c) ⊓ (b ⊔ c)
      apply le_trans (lemma1 a b c)
      obtain ⟨_h3, h4⟩ := le_antisymm_iff.mp (h c a b)
      simp only [sup_comm] at h4
      apply le_trans h4
      simp only [inf_comm, sup_comm]
      exact le_rfl

    · apply le_trans h1
      simp only [ge_iff_le, inf_le_left, sup_of_le_right, true_and]
      apply inf_le_inf le_rfl
      simp only [sup_le_iff, le_sup_right, and_true]
      apply le_sup_of_le_left
      exact inf_le_right
  ·
    intro h a b c
    obtain ⟨h1, h2⟩ := le_antisymm_iff.mp (h (a ⊔ b) a c)
    apply le_antisymm
    · apply le_trans' h2
      simp
      apply le_sup_of_le_right
      simp only [le_inf_iff, inf_le_right, and_true]
      apply le_sup_of_le_right
      exact inf_le_left

    · apply le_trans h1
      simp
      -- changes rhs to a ⊔ b ⊓ c to c ⊓ a ⊔ c ⊓ b
      apply le_trans' (lemma2 _ _ _)
      obtain ⟨h3, h4⟩ := le_antisymm_iff.mp (h c a b)
      rw [inf_comm] at h3
      apply le_trans' h3
      exact le_rfl

-- Phew that was hard
