/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Circuitlib.Circuit.Category.Combinational
public import Circuitlib.Circuit.Basic

@[expose] public section

/-! # Combinational circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

open CategoryTheory
open MonoidalCategory
open OfNat

abbrev CombinationalCircuit := CombinationalCircuitCategory BelnapLevel BelnapGate

namespace CombinationalCircuit

def copyPairBraiding :
    ((ofNat 1 : CombinationalCircuit) ⊗ 1) ⊗ (1 ⊗ 1) ⟶ (1 ⊗ 1) ⊗ (1 ⊗ 1) :=
  let W := (ofNat 1 : CombinationalCircuit)
  (α_ W W (W ⊗ W)).hom ≫
  (W ◁ (α_ W W W).inv) ≫
  (W ◁ ((β_ W W).hom ▷ W)) ≫
  (W ◁ (α_ W W W).hom) ≫
  (α_ W W (W ⊗ W)).inv

def copyPair :
    (ofNat 1 : CombinationalCircuit) ⊗ 1 ⟶
    ((ofNat 1 : CombinationalCircuit) ⊗ 1) ⊗ (1 ⊗ 1) :=
  (CircuitCategory.fork ⊗ₘ CircuitCategory.fork) ≫ copyPairBraiding

def xor : (ofNat 1 : CombinationalCircuit) ⊗ 1 ⟶ 1 :=
  copyPair ≫ (and ⊗ₘ or) ≫ (not ⊗ₘ 𝟙 (ofNat 1 : CombinationalCircuit)) ≫ and

def halfAdder : (ofNat 1 : CombinationalCircuit) ⊗ 1 ⟶ 1 ⊗ 1 := copyPair ≫ (xor ⊗ₘ and)

end CombinationalCircuit

end Circuit
