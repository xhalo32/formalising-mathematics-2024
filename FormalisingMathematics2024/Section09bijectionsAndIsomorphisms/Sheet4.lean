/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# Isomorphisms (of groups, rings, etc)

If `X` and `Y` are types, we have a type `X ≃ Y` of bijections
from `X` to `Y`. If `X` and `Y` additionally have the structure
of groups, or rings, or orders, or topological spaces, or...
then we can furthermore ask that the bijections preserves this
structure.

Just like in the homomorphism case, we don't do this by making
new predicates like `is_group_isomorphism : G ≃ H → Prop`, we do this
by making totally new types called things like `G ≃* H` (group
isomorphisms), `A ≃+* B` (ring isomorphisms) and so on.

Let's see how this works in practice.

-/

-- let A and B be rings
variable (A B : Type) [Ring A] [Ring B]

-- Here's the type (i.e. the set) of all ring isomorphisms from A to B
example : Type :=
  A ≃+* B

-- `A ≃+* B` is notation for `RingEquiv A B`.
-- A ring isomorphism is magically a function (there is a secret coercion going on)
example (φ : A ≃+* B) (a : A) : B :=
  φ a

-- A ring isomorphism is magically a ring homomorphism
example (φ : A ≃+* B) (x y : A) : φ (x + y) = φ x + φ y :=
  map_add φ x y

-- let C be another ring
variable (C : Type) [Ring C]

-- You can compose two ring isomorphisms using RingEquiv.trans
-- here using the power of dot notation
example (φ : A ≃+* B) (ψ : B ≃+* C) : A ≃+* C :=
  φ.trans ψ

-- How do you make a ring isomorphism from two invertible ring homomorphisms?
example (φ : A →+* B) (ψ : B →+* A) (h1 : ∀ a, ψ (φ a) = a) (h2 : ∀ b, φ (ψ b) = b) : A ≃+* B :=
  { toFun := φ
    invFun := ψ
    left_inv := h1
    right_inv := h2
    map_add' := φ.map_add
    map_mul' := φ.map_mul }

-- Notice that `RingEquiv` *extends* `Equiv`, so you need to fill in the `Equiv` fields and then
-- add in the proofs that `φ(a+b)=φ(a)+φ(b)` and `φ(ab)=φ(a)φ(b)`.
-- Note that we never used that ψ was a ring homomorphism! It follows from the fact that ψ is
-- a bijection whose inverse is a ring homomorphism. But of course Lean knows that the inverse of a
-- ring isomorphism is a ring homomorphism -- it's just a theorem, rather than an axiom.
example (φ : A ≃+* B) (x y : B) : φ.symm (x * y) = φ.symm x * φ.symm y :=
  map_mul φ.symm x y



-- ChatGPT exercises:


/-

# Isomorphisms (of groups, rings, etc)

We recall:

- `X ≃ Y` is the type of bijections between types `X` and `Y`.
- For a group structure, we have `G ≃* H` (notation for `MulEquiv G H`).
- For a ring structure, we have `A ≃+* B` (notation for `RingEquiv A B`).

In each case, the equivalence not only is a bijection of the underlying sets,
but it also *preserves the algebraic operations* (multiplication, addition, etc.).

Below are some exercises illustrating how to work with these structures in Lean.
Fill in the `sorry` proofs, or replace them with the appropriate theorems/lemmas.
-/

/-!
## Part 1: Group Isomorphisms
-/

section GroupIsomorphisms

variables {G H K : Type} [Group G] [Group H] [Group K]

/--
A *group isomorphism* from `G` to `H` is a group homomorphism which is also bijective.
Lean's type for group isomorphisms is `G ≃* H` (notation for `MulEquiv G H`).
-/
example : Type :=
  G ≃* H

/--
Lean automatically treats `φ : G ≃* H` as a function `G → H` via a coercion.
-/
example (φ : G ≃* H) (g : G) : H :=
  φ g

/--
Lean also knows that `φ : G ≃* H` is a group homomorphism, so we can use `map_mul φ`.
-/
example (φ : G ≃* H) (g₁ g₂ : G) : φ (g₁ * g₂) = φ g₁ * φ g₂ :=
  map_mul φ g₁ g₂

/--
A group isomorphism also preserves the identity element.
-/
example (φ : G ≃* H) : φ 1 = 1 :=
  map_one φ

/--
A group isomorphism also preserves inverses.
-/
example (φ : G ≃* H) (g : G) : φ g⁻¹ = (φ g)⁻¹ :=
  map_inv φ g

/--
Group isomorphisms compose via `MulEquiv.trans`.
-/
example (φ : G ≃* H) (ψ : H ≃* K) : G ≃* K :=
  φ.trans ψ

/--
How do you construct a group isomorphism if you have a bijective group homomorphism?
You need to supply:
- a forward function `φ : G →* H` (a group homomorphism),
- an inverse function `ψ : H →* G`,
- and proofs that `ψ ∘ φ = id` and `φ ∘ ψ = id`.

You do *not* need to prove that `ψ` is a homomorphism; it follows from the fact that
it will be the inverse of a group isomorphism.
-/
example (φ : G →* H) (ψ : H →* G)
  (h1 : ∀ g, ψ (φ g) = g)
  (h2 : ∀ h, φ (ψ h) = h) :
  G ≃* H :=
{ toFun    := φ
  invFun   := ψ
  left_inv := h1
  right_inv := h2
  map_mul' := φ.map_mul }

/--
### Exercise (easy):
Show that if `φ : G ≃* G` is a group isomorphism from a group to itself, then `φ` is injective.
(Hint: group isomorphisms are always bijective, so you can just apply `MulEquiv.injective φ`.)
-/
example (φ : G ≃* G) : Function.Injective φ := by
  -- cases φ
  have := φ.left_inv
  rw [Function.LeftInverse] at this
  intro x y h
  rw [← this x, ← this y]
  -- change Equiv.toFun φ.toEquiv x = Equiv.toFun φ.toEquiv y at h -- why can't I rewrite `h` directly?

  dsimp -- aha this is why dsimp is useful, it doesn't simplify away the rewrites I just did
  rw [h]

/--
### Exercise (medium):
Show that if `G` and `H` are isomorphic groups (`G ≃* H`), then they have the
"same number" of elements in any finite case. In Lean, you can prove
`Fintype.card G = Fintype.card H` when `G ≃* H` and both are finite.
(Hint: use the fact that a bijection between finite types preserves cardinalities.)
-/
example [Fintype G] [Fintype H] (φ : G ≃* H) : Fintype.card G = Fintype.card H := by
  rw [← Fintype.ofEquiv_card]
  congr
  apply Subsingleton.elim -- two elements of subsingletons must be equal (it's the elimination rule)
  -- apply Fintype.card_congr -- found here
  exact φ.toEquiv

end GroupIsomorphisms

/-!
## Part 2: Ring Isomorphisms
-/

section RingIsomorphisms

variables {A B C : Type} [Ring A] [Ring B] [Ring C]

/--
A *ring isomorphism* from `A` to `B` is a ring homomorphism which is also bijective.
Lean's type for ring isomorphisms is `A ≃+* B` (notation for `RingEquiv A B`).
-/
example : Type :=
  A ≃+* B

/--
Lean treats `φ : A ≃+* B` as a function `A → B`.
-/
example (φ : A ≃+* B) (a : A) : B :=
  φ a

/--
A ring isomorphism preserves addition and multiplication:
-/
example (φ : A ≃+* B) (x y : A) : φ (x + y) = φ x + φ y :=
  map_add φ x y

example (φ : A ≃+* B) (x y : A) : φ (x * y) = φ x * φ y :=
  map_mul φ x y

/--
We can compose two ring isomorphisms using `RingEquiv.trans`.
-/
example (φ : A ≃+* B) (ψ : B ≃+* C) : A ≃+* C :=
  φ.trans ψ

/--
Constructing a ring isomorphism from a bijective ring homomorphism and its inverse.
-/
example (φ : A →+* B) (ψ : B →+* A)
  (h1 : ∀ a, ψ (φ a) = a)
  (h2 : ∀ b, φ (ψ b) = b) :
  A ≃+* B :=
{ toFun    := φ
  invFun   := ψ
  left_inv := h1
  right_inv := h2
  map_add' := φ.map_add
  map_mul' := φ.map_mul }

/--
A ring isomorphism also preserves `0` and `1`.
-/
example (φ : A ≃+* B) : φ 0 = 0 :=
  map_zero φ

example (φ : A ≃+* B) : φ 1 = 1 :=
  map_one φ

/--
It also preserves negatives:
-/
example (φ : A ≃+* B) (a : A) : φ (-a) = -φ a :=
  map_neg φ a

/--
And subtraction:
-/
example (φ : A ≃+* B) (a b : A) : φ (a - b) = φ a - φ b :=
  map_sub φ a b

#check AddEquiv

/--
### Exercise (easy):
Show that if `A` and `B` are isomorphic rings (i.e. `A ≃+* B`), then they have isomorphic
additive groups. (Hint: you can coerce a `RingEquiv A B` to a `AddEquiv A B` using
`φ.toAddEquiv`.)
-/
example (φ : A ≃+* B) : AddEquiv A B := by
  exact φ.toAddEquiv

/--
### Exercise (medium):
Show that if `φ : A ≃+* B`, then `φ` sends units of `A` to units of `B`.

The notation `Aˣ` is used for the `Units` of `A`.
An element of a `Monoid` is a unit if it has a two-sided inverse.

`IsUnit x` is a predicate stating that `x : A` is one of the elements in `Aˣ`.
As a predicate, it doesn't bundle the actual information about the inverse element.
-/
example (φ : A ≃+* B) (u : Aˣ) : IsUnit (φ u) := by
  let bu : Bˣ := ⟨φ u, φ u.inv, ?_, ?_⟩
  · use bu
    -- rw [← hu]
  · rw [← φ.map_mul]
    rw [u.val_inv]
    rw [φ.map_one]
  · rw [← φ.map_mul]
    rw [u.inv_val]
    rw [φ.map_one]

end RingIsomorphisms
