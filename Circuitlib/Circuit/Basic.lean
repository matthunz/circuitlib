/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Circuitlib.Circuit.Category.Basic
public import Circuitlib.Circuit.Belnap.Gate
public import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section

/-! # Circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

open CategoryTheory
open OfNat

universe u

variable
  {C : Type u}
  [∀ n, OfNat C n]
  [Category C]
  [MonoidalCategory C]
  [CircuitCategory BelnapLevel BelnapGate C]

@[simp]
def and : (ofNat 2 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.and

@[simp]
def or : (ofNat 2 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.or

@[simp]
def not : (ofNat 1 : C) ⟶ 1 := CircuitCategory.gate BelnapGate.not

open MonoidalCategory

def nand : (ofNat 2 : C) ⊗ 1 ⟶ 1 ⊗ 1 := and ⊗ₘ not

def nor : (ofNat 2 : C) ⊗ 1 ⟶ 1 ⊗ 1 := or ⊗ₘ not

end Circuit
