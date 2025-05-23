/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.PrincipalIdealDomain
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/
variable (R : Type) [CommRing R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain.
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":
variable [IsPrincipalIdealRing R] [IsDomain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.
example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b
  apply eq_zero_or_eq_zero_of_mul_eq_zero

-- typeclass inference
-- magically extracts the assumption from `IsDomain`
example : (0 : R) ≠ 1 := by
  intro c
  exact zero_ne_one c

example (I : Ideal R) : I.IsPrincipal := by
  exact IsPrincipalIdealRing.principal I

#check Ideal.span_singleton_generator
example (I : Ideal R) : ∃ j, I = Ideal.span {j} := by
  rw [← I.span_singleton_generator]
  exact Submodule.IsPrincipal.principal (Ideal.span {Submodule.IsPrincipal.generator I})

#check Ideal.prod_span
#check Submodule.span
#check Ideal.submodule_span_eq
#check Submodule.prod
-- #check Ideal.map_eq_submodule_map
#check Submodule.span
#check Submodule.IsPrincipal

-- #check Ideal.prod


-- From modern mathlib
namespace Ideal

variable {R : Type*} {S : Type*} [Semiring R] [Semiring S] (I : Ideal R) (J : Ideal S)

/-- `I × J` as an ideal of `R × S`. -/
def prod : Ideal (R × S) := I.comap (RingHom.fst R S) ⊓ J.comap (RingHom.snd R S)

@[simp]
theorem mem_prod {r : R} {s : S} : (⟨r, s⟩ : R × S) ∈ prod I J ↔ r ∈ I ∧ s ∈ J :=
  Iff.rfl

@[simp]
theorem prod_top_top : prod (⊤ : Ideal R) (⊤ : Ideal S) = ⊤ :=
  Ideal.ext <| by simp

/-- Every ideal of the product ring is of the form `I × J`, where `I` and `J` can be explicitly
    given as the image under the projection maps. -/
theorem ideal_prod_eq (I : Ideal (R × S)) :
    I = Ideal.prod (map (RingHom.fst R S) I : Ideal R) (map (RingHom.snd R S) I) := by
  apply Ideal.ext
  rintro ⟨r, s⟩
  rw [mem_prod, mem_map_iff_of_surjective (RingHom.fst R S) Prod.fst_surjective,
    mem_map_iff_of_surjective (RingHom.snd R S) Prod.snd_surjective]
  refine ⟨fun h => ⟨⟨_, ⟨h, rfl⟩⟩, ⟨_, ⟨h, rfl⟩⟩⟩, ?_⟩
  rintro ⟨⟨⟨r, s'⟩, ⟨h₁, rfl⟩⟩, ⟨⟨r', s⟩, ⟨h₂, rfl⟩⟩⟩
  simpa using I.add_mem (I.mul_mem_left (1, 0) h₁) (I.mul_mem_left (0, 1) h₂)

end Ideal

variable (A B : Type) [CommRing A] [CommRing B]

-- This is the projection that we need
#check Ideal.map (RingHom.fst A B)

-- For the other direction, this is too general, we need just pairwise product
#check Ideal.prod_span
#check Ideal.span_le
#check Ideal.ideal_prod_eq
#check Ideal.prod_span_singleton
#check Ideal.span_singleton_mul_span_singleton
#check Ideal.span_singleton_mul_eq_span_singleton_mul
#check Ideal.span_mul_span

#check Ideal.comap_inf

lemma prod_span_span {A B : Type*} [CommRing A] [CommRing B] (a : A) (b : B) :
  Ideal.prod (Ideal.span {a}) (Ideal.span {b}) = Ideal.span {(a, b)} := by
  rw [Ideal.prod]
  apply le_antisymm
  · intro x ⟨h1, h2⟩
    simp at h1 h2
    rw [Ideal.mem_span_singleton] at *
    rcases h1 with ⟨r₁, hr₁⟩
    rcases h2 with ⟨r₂, hr₂⟩
    use (r₁, r₂)
    ext <;> simp [hr₁, hr₂]

  · apply Submodule.span_le.2
    simp [Set.mem_preimage]
    simp [Ideal.mem_span]

/-
The above is now available in Mathlib in more generality:
https://github.com/leanprover-community/mathlib4/pull/25118
-/
@[simp]
theorem bot_prod_bot {R S : Type*} [Semiring R] [Semiring S] : (⊥ : Ideal R).prod (⊥ : Ideal S) = ⊥ :=
  SetLike.coe_injective <| Set.singleton_prod_singleton

theorem span_prod_span {R S : Type*} [Semiring R] [Semiring S] {s : Set R} {t : Set S} (hst : s.Nonempty ↔ t.Nonempty) :
    Ideal.prod (Ideal.span s) (Ideal.span t) = Ideal.span (s ×ˢ t) := by
  simp_rw [iff_iff_and_or_not_and_not, Set.not_nonempty_iff_eq_empty] at hst
  obtain ⟨hs, ht⟩ | ⟨rfl, rfl⟩ := hst
  · conv_rhs => rw [Ideal.ideal_prod_eq (Ideal.span (s ×ˢ t))]
    congr 1
    · rw [Ideal.map_span]
      simp [Set.fst_image_prod _ ht]
    · rw [Ideal.map_span]
      simp [Set.snd_image_prod hs]
  · simp

-- product of two PIDs isn't a PID, but only becuase it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [insta : IsPrincipalIdealRing A] [instb : IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := by
    let Ia := Ideal.map (RingHom.fst A B) I
    let Ib := Ideal.map (RingHom.snd A B) I

    have pa := insta.principal Ia
    have pb := instb.principal Ib

    simp_rw [Submodule.isPrincipal_iff] at *
    obtain ⟨a, ha⟩ := pa
    obtain ⟨b, hb⟩ := pb
    use ⟨a, b⟩
    rw [Ideal.ideal_prod_eq I]
    rw [ha, hb]
    simp [Ideal.span]
    -- apply prod_span_span -- key lemma!

    rw [← Set.singleton_prod_singleton]
    apply span_prod_span -- Generalization of the key lemma :D
    simp only [Set.singleton_nonempty]
