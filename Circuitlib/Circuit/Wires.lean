/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

/-! # Wires

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

def Wires (V : Type u) (I : ℕ) := Vector V I

instance [Preorder V] : Preorder (Wires V I) where
  le a b := ∀ i : Fin I, a.get i ≤ b.get i
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)
  lt_iff_le_not_ge _ _ := by rfl

end Circuit
