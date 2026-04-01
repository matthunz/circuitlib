/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Circuitlib.Circuit.Category.Combinational
public import Mathlib.Data.Stream.Defs

@[expose] public section

/-! # Sequential circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- Category of sequential circuits. -/
structure SequentialCircuitCategory (V : Type*) (G : Type*) where of (V) (G) ::
  obj : ℕ

attribute [inline, simp] SequentialCircuitCategory.obj

@[simp]
instance : OfNat (SequentialCircuitCategory V G) n where
  ofNat := .of V G n

namespace SequentialCircuitCategory

def Stream := Stream'

instance [Preorder α] : Preorder (Stream α) where
  le xs ys := (xs.zip (fun x y => (x, y)) ys).All ((fun (x, y) => x <= y))
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)

universe u v

variable {V : Type v} {G : Type u}

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : SequentialCircuitCategory V G) :=
  { f : Stream (Wires V I.obj) → Stream (Wires V O.obj) // Monotone f }

@[inline, simp]
def id_val : Stream (Wires V n) → Stream (Wires V n) := fun x => x

@[simp]
lemma id_monotone [Preorder V] : Monotone (id_val (V:=V) (n:=n)) := monotone_id

@[inline, simp]
def id [Preorder V] : SequentialCircuitCategory.Hom V X X := ⟨id_val, id_monotone⟩

open CategoryTheory

@[inline, simp]
instance [Preorder V] : Category.{v} (SequentialCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val, Monotone.comp g.property f.property⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end SequentialCircuitCategory

end Circuit
