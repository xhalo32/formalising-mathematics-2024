/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section7sheet1

/-!

# Review of subgroups

In Lean, a subgroup is not a group. This is for the same reason that a subset
is not a type. The way subgroups work is that if `G` is a group:

`variables (G : Type) [Group G]`

then the type of *all* subgroups of `G` is called `Subgroup G`. So if you want
one subgroup of G:

`variable (H : Subgroup G)`

then, as you can see, `H` is not a type (we don't write `H : Type`), it's a term.
So how do we do elements of `H` then? It's just the same as sets: an element `x` of
`H` is a term `x` of type `G`, such that the proposition `x ∈ H` holds.

Here's the basic API for subgroups.
-/

-- Let `G` be a group, let `a` and `b` be elements of `H`, and let `H` and `K` be subgroups of `G`.
variable (G : Type) [Group G] (a b : G) (H K : Subgroup G)

-- The basic API for subgroups
example : (1 : G) ∈ H :=
  one_mem H

example (ha : a ∈ H) : a⁻¹ ∈ H :=
  inv_mem ha

example (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  mul_mem ha hb

-- Let's use these axioms to make more API for subgroups.
-- First, see if you can put the axioms together to prove subgroups are closed under "division".
example (ha : a ∈ H) (hb : b ∈ H) : a * b⁻¹ ∈ H := by
  exact mul_mem ha (inv_mem hb)

-- Now try these. You might want to remind yourself of the API for groups as explained
-- in an earlier section, or make use of the `group` tactic.
-- This lemma is called `Subgroup.inv_mem_iff` but try proving it yourself
example : a⁻¹ ∈ H ↔ a ∈ H := by
  constructor
  · intro h
    apply inv_mem at h
    rw [inv_inv] at h
    exact h
  · exact inv_mem

-- this is `mul_mem_cancel_left` but see if you can do it from the axioms of subgroups.
-- Again feel free to use the `group` tactic.
example (ha : a ∈ H) : a * b ∈ H ↔ b ∈ H := by
  constructor
  · intro hab
    apply inv_mem at ha
    apply mul_mem ha at hab
    simp only [← mul_assoc, inv_mul_self, one_mul] at hab
    exact hab
  · apply mul_mem ha

/-

## Complete lattice structure on subgroups of G

The reason I'm banging on about subgroups again, is that
they form a complete lattice. Let's just check this:

-/
example : CompleteLattice (Subgroup G) := by
  infer_instance

/-

The "type class inference system" (the system which deals with square bracket inputs to
functions) already knows this. The `infer_instance` tactic means "find this
construction in the database".

Because subgroups are a complete lattice, there will be a smallest subgroup `⊥` of `G`
and a largest subgroup `⊤`. You can guess what these are (note that `⊥` isn't the empty set,
this isn't a subgroup). Let's get the hang of these subgroups. Here's their API
(by the way, I don't have a clue about these APIs, I don't have them all committed to memory,
I just write down the natural statements and then either guess the names of the proofs or
use `exact?`):

-/
example : a ∈ (⊥ : Subgroup G) ↔ a = 1 :=
  Subgroup.mem_bot

example : a ∈ (⊤ : Subgroup G) :=
  Subgroup.mem_top a

/-

# Conjugating a subgroup by an element.

Let's define the conjugate `xHx⁻¹` of a subgroup `H` by an element `x`. To do this we
are going to have to know how to *make* subgroups, not just prove things about subgroups.

To create a subgroup of `G`, you need to give a subset of `G` and then a proof
that the subset satisfies the three axioms `one_mem`, `inv_mem` and `mul_mem` for subgroups.
If `H : subgroup G` and `x : G` then the *conjugate* of `H` by `x` is
the set `{a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}`. So let's show that this set
satisfies the axioms for a subgroup.

-/
variable {G H} {x : G}

variable {y z : G}

theorem conjugate.one_mem : (1 : G) ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  rw [Set.mem_setOf]
  use x⁻¹ * x
  group
  simp only [and_true]
  exact H.one_mem

theorem conjugate.inv_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
    y⁻¹ ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  obtain ⟨y', yh, hy⟩ := hy
  rw [Set.mem_setOf]
  use y'⁻¹
  constructor
  · exact H.inv_mem yh
  · rw [hy]
    rw [conj_inv] -- ooh shiny

theorem conjugate.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹})
    (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
    y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  obtain ⟨y', yh, hy⟩ := hy
  obtain ⟨z', zh, hz⟩ := hz
  rw [Set.mem_setOf]
  use y' * z'
  constructor
  · exact H.mul_mem yh zh
  · rw [hy, hz]
    rw [conj_mul] -- these are quite convenient :D

-- Now here's the way to put everything together:
def conjugate (H : Subgroup G) (x : G) : Subgroup G
    where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := conjugate.one_mem
  inv_mem' := conjugate.inv_mem
  mul_mem' := conjugate.mul_mem

/-

## The cost of a definition

You might think "we're done with conjugates now". But not so fast!

If we were putting the definition of `conjugate` into mathlib then the next thing we would have to
do would be to prove a whole bunch of things about it. Every definition in a formalised system
comes with a cost. If you just make the definition and don't prove theorems about it,
then other people can't use your definition easily in their theorems.

What kind of theorems would we want to prove about conjugates? We might want to prove
that if `H ≤ K` then `conjugate H x ≤ conjugate K x`. We might want to prove
that `conjugate ⊥ x = ⊥` and `conjugate ⊤ x = ⊤`. And we might want to prove
that if `G` is abelian then `conjugate H x = H` for all `H`. Before we embark on this,
I had better tell you how to prove that two subgroups of a group are equal in Lean.
To check two subgroups are equal it suffices to prove they have the same elements:
this is called "extensionality" for subgroups, and you can make this step using the `ext`
tactic. I'll show you below.

Let's make some API for conjugates. I'll suggest some names for the lemmas.

-/
-- This one is always handy: you will be able to `rw` it when faced with goals
-- of the form `a ∈ conjugate H x`.
theorem mem_conjugate_iff : a ∈ conjugate H x ↔ ∃ h, h ∈ H ∧ a = x * h * x⁻¹ := by
  -- true by definition!
  rfl

theorem conjugate_mono (H K : Subgroup G) (h : H ≤ K) : conjugate H x ≤ conjugate K x := by
  intro w wh
  obtain ⟨w', wh, hw⟩ := wh
  use w'
  rw [hw]
  exact ⟨h wh, rfl⟩

theorem conjugate_bot : conjugate ⊥ x = ⊥ := by
  ext w
  constructor
  · intro wh
    obtain ⟨w', wh, hw⟩ := wh
    cases wh -- must be 1
    group at hw
    exact hw
  · rintro ⟨rfl⟩
    -- exact Subgroup.one_mem -- doesn't work???
    apply Subgroup.one_mem -- but this does
    -- exact @Subgroup.one_mem G _ _ -- works too

theorem conjugate_top : conjugate ⊤ x = ⊤ := by
  ext w
  constructor
  · intro wh
    exact trivial
  · intro
    refine ⟨x⁻¹ * w * x, Subgroup.mem_top w, ?_⟩
    group

theorem conjugate_eq_of_abelian (habelian : ∀ a b : G, a * b = b * a) : conjugate H x = H := by
  ext w
  constructor
  · intro wh
    obtain ⟨w', wh, hw⟩ := wh
    rw [habelian, ← mul_assoc, inv_mul_self, one_mul] at hw
    cases hw
    exact wh
  · intro h
    use w
    refine ⟨h, ?_⟩
    rw [habelian, ← mul_assoc, inv_mul_self, one_mul]


-- Now for some normal subgroups!



-- Conjugating a normal subgroup by an element of the subgroup gets a normal subgroup.
theorem normal_conjugate {N : Subgroup G} (g : G) {hn : Subgroup.Normal N} (hg : g ∈ N) : Subgroup.Normal (conjugate N g) where
  conj_mem n nh g' := by
    rw [mem_conjugate_iff] at *
    obtain ⟨h, hh, rfl⟩ := nh
    use g⁻¹ * (g' * g * h * g⁻¹ * g'⁻¹) * g -- inside parens is the lhs
    refine ⟨?_, by group⟩
    suffices (g⁻¹ * g' * g) * h * (g⁻¹ * g' * g)⁻¹ ∈ N by
      group at this
      group
      exact this
    apply hn.conj_mem _ hh

end Section7sheet1
