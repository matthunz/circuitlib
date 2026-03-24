/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Circuitlib.Circuit.Category
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-! # Combinational circuits

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- Category of combinational circuits. -/
structure CombinationalCircuit (V : Type*) (G : Type*) where of (V) (G) ::
  obj : ℕ

instance : OfNat (CombinationalCircuit V G) n where
  ofNat := .of V G n

namespace CombinationalCircuit

universe u v

variable {V : Type v} {G : Type u}

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : CombinationalCircuit V G) :=
  { f : Wires V I.obj → Wires V O.obj // Monotone f }

def Hom.id [Preorder V] : CombinationalCircuit.Hom V X X := ⟨fun x => x, monotone_id⟩

open CategoryTheory

instance [Preorder V] : Category.{v} (CombinationalCircuit V G) where
  Hom := Hom V
  id _ := Hom.id
  comp f g := ⟨g.val ∘ f.val, Monotone.comp g.property f.property⟩
  id_comp _ := by rfl
  comp_id _ := by rfl
  assoc _ _ _ := by rfl

def drop (_ : Wires V 1) : Wires V 0 := #v[]

@[simp]
lemma drop_monotone [Preorder V] : Monotone (drop (V:=V)) := fun _ _ _ => le_refl _

def fork (w : Wires V 1) : Wires V 2 := #v[w.get 0, w.get 0]

@[simp]
lemma fork_monotone [Preorder V] : Monotone (fork (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> exact h 0

def join [SemilatticeSup V] (w : Wires V 2) : Wires V 1 := #v[w.get 0 ⊔ w.get 1]

@[simp]
lemma join_monotone [SemilatticeSup V] : Monotone (join (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 := by omega
  subst this; exact sup_le_sup (h 0) (h 1)

@[simp]
def tensorObj (X Y : CombinationalCircuit V G) : CombinationalCircuit V G :=
  .of V G (X.obj + Y.obj)

variable [SemilatticeSup V]

instance [Gate V G] [Bot V] : CircuitCategory V G (CombinationalCircuit V G) where
  gate g := ⟨Gate.gate g, Gate.gate_monotone g⟩
  stub := ⟨fun _ => #v[⊥], fun _ _ _ => le_refl _⟩
  drop := ⟨drop, drop_monotone⟩
  fork := ⟨fork, fork_monotone⟩
  join := ⟨join, join_monotone⟩

@[simp]
lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (Vector.append (f.val (Vector.ofFn fun i => Vector.get a (Fin.castAdd X₂.obj i)))
      (g.val (Vector.ofFn fun i => Vector.get a (Fin.natAdd X₁.obj i)))).get
      (Fin.castAdd Y₂.obj j) =
    Vector.get (f.val (Vector.ofFn fun i => Vector.get a (Fin.castAdd X₂.obj i))) j := by
  have hf := (f.val (Vector.ofFn (fun i => a.get (i.castAdd _)))).size_toArray
  simp only [Vector.get, Vector.append, Fin.val_cast, Fin.val_castAdd] at hf ⊢
  exact Array.getElem_append_left (by omega)

@[simp]
lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (Vector.append (f.val (Vector.ofFn fun i => Vector.get a (Fin.castAdd X₂.obj i)))
      (g.val (Vector.ofFn fun i => Vector.get a (Fin.natAdd X₁.obj i)))).get
      (Fin.natAdd Y₁.obj j) =
    Vector.get (g.val (Vector.ofFn fun i => Vector.get a (Fin.natAdd X₁.obj i))) j := by
  have hf := (f.val (Vector.ofFn (fun i => a.get (i.castAdd _)))).size_toArray
  simp only [Vector.get, Vector.append, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] at hf ⊢
  rw [Array.getElem_append_right (by omega)]
  congr 1; omega

lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (a b : Wires V (X₁.obj + X₂.obj))
    (h : a ≤ b)
    (i : Fin (Y₁.obj + Y₂.obj)) :
      ((fun v =>
          Vector.append (f.val (Vector.ofFn fun i => Vector.get v (Fin.castAdd X₂.obj i)))
            (g.val (Vector.ofFn fun i => Vector.get v (Fin.natAdd X₁.obj i)))) a).get i ≤
        ((fun v =>
           Vector.append (f.val (Vector.ofFn fun i => Vector.get v (Fin.castAdd X₂.obj i)))
            (g.val (Vector.ofFn fun i => Vector.get v (Fin.natAdd X₁.obj i)))) b).get i :=
  Fin.addCases
    (fun j => by
      have lhs_eq := tensorHom_eq_left a j f g
      have rhs_eq := tensorHom_eq_left b j f g
      rw [lhs_eq, rhs_eq]
      exact f.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn, Fin.eta]
        exact h (k.castAdd _)) j)
    (fun j => by
      have lhs_eq := tensorHom_eq_right a j f g
      have rhs_eq := tensorHom_eq_right b j f g
      rw [lhs_eq, rhs_eq]
      exact g.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn, Fin.eta]
        exact h (k.natAdd _)) j)
    i

@[simp]
def tensorHomVal
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Wires V (X₁.obj + X₂.obj)) :
    Wires V (Y₁.obj + Y₂.obj) :=
  (f.val (Vector.ofFn (fun i => v.get (i.castAdd _)))).append
    (g.val (Vector.ofFn (fun i => v.get (i.natAdd _))))

@[simp]
lemma tensorHomVal_castAdd
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (w : Wires V (X₁.obj + X₂.obj)) (j : Fin Y₁.obj) :
    (tensorHomVal f g w).get (Fin.castAdd Y₂.obj j) =
    (f.val (Vector.ofFn fun k => w.get (Fin.castAdd X₂.obj k))).get j :=
  tensorHom_eq_left w j f g

@[simp]
lemma tensorHomVal_natAdd
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (w : Wires V (X₁.obj + X₂.obj)) (j : Fin Y₂.obj) :
    (tensorHomVal f g w).get (Fin.natAdd Y₁.obj j) =
    (g.val (Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k))).get j :=
  tensorHom_eq_right w j f g

@[simp]
def tensorHom
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHomVal f g, tensorHom_monotone f g⟩

@[simp]
def iso (h : n = m) : CombinationalCircuit.of V G n ≅ CombinationalCircuit.of V G m :=
  { hom := ⟨(·.cast h), fun _ _ hab i => hab (i.cast h.symm)⟩
    inv := ⟨(·.cast h.symm), fun _ _ hab i => hab (i.cast h)⟩
    hom_inv_id := by apply Subtype.ext; funext v; rfl
    inv_hom_id := by apply Subtype.ext; funext v; rfl }

@[simp]
lemma whisker
    (X Y : CombinationalCircuit V G) :
    tensorHom (𝟙 X) Hom.id = 𝟙 (CombinationalCircuit.of V G (X.obj + Y.obj)) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X) (𝟙 Y) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X) (𝟙 Y)]
    dsimp only [CategoryStruct.id, Hom.id]; rw [Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X) (𝟙 Y)]
    dsimp only [CategoryStruct.id, Hom.id]; rw [Wires.get_ofFn]

@[simp]
def whiskerLeft
    (X Y₁ Y₂ : CombinationalCircuit V G) :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom Hom.id

@[simp]
def whiskerRight
    (f : X₁ ⟶ X₂)
    (Y : CombinationalCircuit V G) :
    (tensorObj X₁ Y ⟶ tensorObj X₂ Y) :=
  tensorHom f Hom.id

@[simp]
lemma tensorHom_def
    {W X Y Z : CombinationalCircuit V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ X.whiskerLeft Y Z g := by
  apply Subtype.ext; funext v
  change tensorHomVal f g v = tensorHomVal Hom.id g (tensorHomVal f Hom.id v)
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j f g, tensorHom_eq_left _ j Hom.id g]
    simp only [Hom.id]; rw [Wires.get_ofFn]
    exact (tensorHom_eq_left v j f Hom.id).symm
  · rw [tensorHom_eq_right v j f g, tensorHom_eq_right _ j Hom.id g]
    simp only [Hom.id]
    exact congrArg (fun x => (g.val x).get j)
      (Wires.ext (fun k => by
        conv_rhs => rw [Wires.get_ofFn]
        exact (tensorHom_eq_right v k f (𝟙 _)).symm))

@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : CombinationalCircuit V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X₁) (𝟙 X₂) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X₁) (𝟙 X₂)]
    dsimp only [CategoryStruct.id, Hom.id]; rw [Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X₁) (𝟙 X₂)]
    dsimp only [CategoryStruct.id, Hom.id]; rw [Wires.get_ofFn]

@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CombinationalCircuit V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal g₁ g₂ (tensorHomVal f₁ f₂ v) = tensorHomVal (f₁ ≫ g₁) (f₂ ≫ g₂) v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ j g₁ g₂, tensorHom_eq_left v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    dsimp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₁.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_left v k f₁ f₂))
  · rw [tensorHom_eq_right _ j g₁ g₂, tensorHom_eq_right v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    dsimp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₂.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_right v k f₁ f₂))

@[simp]
def tensorUnit : CombinationalCircuit V G := .of V G 0

@[simp]
def associator
    (X Y Z : CombinationalCircuit V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  let h := Nat.add_assoc X.obj Y.obj Z.obj
  { hom := ⟨(·.cast h), fun _ _ hab i => hab (i.cast h.symm)⟩
    inv := ⟨(·.cast h.symm), fun _ _ hab i => hab (i.cast h)⟩
    hom_inv_id := by apply Subtype.ext; funext v; rfl
    inv_hom_id := by apply Subtype.ext; funext v; rfl }

@[simp]
lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CombinationalCircuit V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [Vector.get, CategoryStruct.comp, tensorHomVal, tensorHom, associator,
              Vector.cast, Vector.append, Vector.toArray_ofFn, Array.getElem_ofFn,
              Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast, Function.comp,
              Array.append_assoc]
  simp only [tensorObj, show (X₁ + X₂).obj = X₁.obj + X₂.obj from rfl,
              Nat.add_assoc]

@[simp]
lemma pentagon
    (W X Y Z : CombinationalCircuit V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      W.whiskerLeft
        ((X.tensorObj Y).tensorObj Z)
        (X.tensorObj (Y.tensorObj Z))
        (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [tensorHom, tensorHomVal, tensorObj, whiskerLeft, whiskerRight, associator,
              Vector.get, CategoryStruct.comp, Vector.cast, Vector.append, Vector.toArray_ofFn,
              Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast, Function.comp,
              Hom.id]
  have vec_arr : ∀ {n} (v : Vector V n) (j : Nat) (hj : j < n),
      v[j] = v.toArray[j]'(by rw [v.size_toArray]; exact hj) := fun _ _ _ => rfl
  simp only [vec_arr]
  have hWXY : (W.obj + X.obj + Y.obj) =
      W.obj + X.obj + Y.obj := rfl
  have hXYZ : (X.obj + (Y.obj + Z.obj)) =
      X.obj + (Y.obj + Z.obj) := rfl
  have hN : (CombinationalCircuit.of V G (W.obj + (X.obj + (Y.obj + Z.obj)))).obj =
      W.obj + (X.obj + (Y.obj + Z.obj)) := rfl
  rcases Nat.lt_or_ge i W.obj with h₁ | h₁
  · rw [Array.getElem_append_left
          (by simp only [Vector.getElem_toArray, Array.size_ofFn]; exact h₁),
        Array.getElem_ofFn,
        Array.getElem_append_left (by simp [Array.size_ofFn]; omega),
        Array.getElem_ofFn]
  · rw [Array.getElem_append_right (by simp [Array.size_ofFn]; omega)]
    simp only [Array.getElem_ofFn, Array.size_ofFn]
    rcases Nat.lt_or_ge i (W.obj + X.obj + Y.obj) with h₂ | h₂
    · rw [Array.getElem_append_left (by simp [Array.size_ofFn]; omega)]
      simp only [Array.getElem_ofFn]
      congr 1; omega
    · rw [Array.getElem_append_right (by simp [Array.size_ofFn]; omega)]
      simp only [Array.getElem_ofFn, Array.size_ofFn]
      congr 1; omega

@[simp]
lemma leftUnitor_naturality
    {X Y : CombinationalCircuit V G} (f : X ⟶ Y) :
    tensorUnit.whiskerLeft X Y f ≫ (iso (Nat.zero_add Y.obj : 0 + Y.obj = Y.obj)).hom =
    (iso (Nat.zero_add X.obj : 0 + X.obj = X.obj)).hom ≫ f := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  dsimp only [CategoryStruct.comp, Function.comp]
  simp only [tensorHom, Vector.get, tensorHomVal, whiskerLeft, Hom.id,
              Vector.append, Vector.toArray_ofFn,
              Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast]
  simp only [Vector.getElem_toArray, Array.ofFn_zero, Array.empty_append]
  exact congrArg (fun x => (f.val x).get ⟨i, hi⟩)
    (by apply Vector.ext; intro j hj; simp)

@[simp]
lemma rightUnitor_naturality
    {X Y : CombinationalCircuit V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (iso (Nat.add_zero Y.obj : Y.obj + 0 = Y.obj)).hom =
    (iso (Nat.add_zero X.obj : X.obj + 0 = X.obj)).hom ≫ f := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  dsimp only [CategoryStruct.comp, Function.comp]
  simp only [tensorHom, whiskerRight, Vector.get, tensorHomVal, Hom.id,
              Vector.append, Vector.toArray_ofFn,
              Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast, Nat.add_zero]
  simp only [Vector.getElem_toArray, Array.ofFn_zero, Array.append_empty, Vector.mk_toArray]
  exact congrArg (fun x => (f.val x).get ⟨i, hi⟩)
    (by apply Vector.ext; intro j hj; simp)

@[simp]
lemma triangle
    (X Y : CombinationalCircuit V G) :
    (X.associator tensorUnit Y).hom ≫
      X.whiskerLeft (tensorUnit.tensorObj Y) Y (iso (Nat.zero_add Y.obj : 0 + Y.obj = Y.obj)).hom =
    whiskerRight (iso (Nat.add_zero X.obj : X.obj + 0 = X.obj)).hom Y := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [tensorObj, tensorHom, whiskerLeft, whiskerRight, iso, associator, Vector.get,
              CategoryStruct.comp, tensorHomVal, Vector.cast, Vector.append, Vector.toArray_ofFn,
              Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast, Function.comp, Hom.id]
  have vec_arr : ∀ {n} (v : Vector V n) (j : Nat) (hj : j < n),
      v[j] = v.toArray[j]'(by rw [v.size_toArray]; exact hj) := fun _ _ _ => rfl
  simp only [vec_arr]
  have h0 : (CombinationalCircuit.of V G 0).obj = 0 := rfl
  have hX0 : (X.obj + ((CombinationalCircuit.of V G 0).obj)) = X.obj + 0 := rfl
  rcases Nat.lt_or_ge i X.obj with h₁ | h₁
  · rw [Array.getElem_append_left
          (by simp only [Vector.getElem_toArray, Array.size_ofFn]; exact h₁),
        Array.getElem_ofFn,
        Array.getElem_append_left (by simp [Array.size_ofFn]; omega),
        Array.getElem_ofFn]
  · rw [Array.getElem_append_right (by simp [Array.size_ofFn]; omega)]
    simp only [Array.getElem_ofFn, Array.size_ofFn]
    rw [Array.getElem_append_right (by simp [Array.size_ofFn]; omega)]
    simp only [Array.getElem_ofFn, Array.size_ofFn]
    congr 1

instance : MonoidalCategory.{v} (CombinationalCircuit V G) where
  tensorObj
  tensorHom
  whiskerLeft
  whiskerRight
  tensorHom_def
  id_tensorHom_id
  tensorHom_comp_tensorHom
  whiskerLeft_id := whisker
  id_whiskerRight := whisker
  tensorUnit
  associator
  associator_naturality
  leftUnitor X := iso (Nat.zero_add X.obj)
  leftUnitor_naturality
  rightUnitor X := iso (Nat.add_zero X.obj)
  rightUnitor_naturality
  pentagon
  triangle

@[simp]
def braiding_hom (X Y : CombinationalCircuit V G) : tensorObj X Y ⟶ tensorObj Y X :=
  ⟨fun v => Vector.ofFn fun i =>
      if h : i.val < Y.obj
      then v.get ⟨X.obj + i.val,
        by change X.obj + i.val < X.obj + Y.obj; omega⟩
      else v.get ⟨i.val - Y.obj, by
        have : i.val < Y.obj + X.obj := i.isLt
        change i.val - Y.obj < X.obj + Y.obj; omega⟩,
      fun a b hab i => by
        simp only [Wires.get_ofFn]; split <;> exact hab _⟩

@[simp]
lemma hom_inv_id
    {X Y : CombinationalCircuit V G} :
    X.braiding_hom Y ≫ Y.braiding_hom X = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, CategoryStruct.id, Hom.id,
              braiding_hom, Wires.get_ofFn]
  split <;> split <;>
    first | (simp only [] at *; omega)
          | exact congrArg v.get (Fin.ext (by simp only []; omega))

@[simp]
def braiding (X Y : CombinationalCircuit V G) : tensorObj X Y ≅ tensorObj Y X :=
  { hom := braiding_hom X Y
    inv := braiding_hom Y X
    hom_inv_id
    inv_hom_id := hom_inv_id }

@[simp]
lemma braiding_get (X Y : CombinationalCircuit V G)
    (v : Wires V (X.obj + Y.obj)) (i : Fin (Y.obj + X.obj)) :
    ((braiding X Y).hom.val v).get i =
      if h : i.val < Y.obj
      then v.get ⟨X.obj + i.val, by omega⟩
      else v.get ⟨i.val - Y.obj, by omega⟩ := by
  unfold braiding braiding_hom; simp only [Wires.get_ofFn]

@[simp]
lemma braiding_get_castAdd (X Y : CombinationalCircuit V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin Y.obj) :
    ((braiding X Y).hom.val v).get (Fin.castAdd X.obj j) =
    v.get (Fin.natAdd X.obj j) := by
  simp only [braiding_get, Fin.val_castAdd, dif_pos j.isLt]
  exact congrArg v.get (Fin.ext (by simp [Fin.val_natAdd]))

@[simp]
lemma braiding_get_natAdd (X Y : CombinationalCircuit V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin X.obj) :
    ((braiding X Y).hom.val v).get (Fin.natAdd Y.obj j) =
    v.get (Fin.castAdd Y.obj j) := by
  simp only [braiding_get, Fin.val_natAdd,
             dif_neg (show ¬(Y.obj + j.val < Y.obj) from by omega)]
  exact congrArg v.get (Fin.ext (by simp [Fin.val_castAdd]))

omit [SemilatticeSup V] in
@[simp]
lemma Wires.get_cast {n m : ℕ} (h : n = m) (v : Wires V n) (i : Fin m) :
    (v.cast h).get i = v.get ⟨i.val, h ▸ i.isLt⟩ := by
  subst h; rfl

@[simp]
lemma associator_hom_val (X Y Z : CombinationalCircuit V G)
    (w : Wires V ((X.obj + Y.obj) + Z.obj)) :
    (MonoidalCategoryStruct.associator X Y Z).hom.val w =
    w.cast (Nat.add_assoc X.obj Y.obj Z.obj) := rfl

@[simp]
lemma associator_inv_val (X Y Z : CombinationalCircuit V G)
    (w : Wires V (X.obj + (Y.obj + Z.obj))) :
    (MonoidalCategoryStruct.associator X Y Z).inv.val w =
    w.cast (Nat.add_assoc X.obj Y.obj Z.obj).symm := rfl

@[simp]
lemma tensorHomVal_get
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuit V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (w : Wires V (X₁.obj + X₂.obj))
    (i : Fin (Y₁.obj + Y₂.obj)) :
    (tensorHomVal f g w).get i =
    if h : i.val < Y₁.obj
    then (f.val (Vector.ofFn fun k => w.get (Fin.castAdd X₂.obj k))).get ⟨i.val, h⟩
    else (g.val (Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k))).get
      ⟨i.val - Y₁.obj, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tensorHomVal_castAdd, Fin.val_castAdd, dif_pos j.isLt]
  · simp only [tensorHomVal_natAdd, Fin.val_natAdd,
               dif_neg (show ¬(Y₁.obj + j.val < Y₁.obj) from by omega)]
    congr 1; exact Fin.ext (by dsimp; omega)

@[simp]
lemma braiding_naturality_left
    {X Y : CombinationalCircuit V G}
    (f : X ⟶ Y)
    (Z : CombinationalCircuit V G) :
    MonoidalCategoryStruct.whiskerRight f Z ≫ (Y.braiding Z).hom =
    (X.braiding Z).hom ≫ MonoidalCategoryStruct.whiskerLeft Z f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp]
  have hwr : ∀ w, (MonoidalCategoryStruct.whiskerRight f Z).val w = tensorHomVal f Hom.id w :=
    fun _ => rfl
  have hwl : ∀ w, (MonoidalCategoryStruct.whiskerLeft Z f).val w = tensorHomVal Hom.id f w :=
    fun _ => rfl
  simp only [hwr, hwl]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [braiding_get_castAdd, tensorHomVal_castAdd, tensorHomVal_natAdd,
                Hom.id, Wires.get_ofFn]
  · simp only [braiding_get_natAdd, tensorHomVal_castAdd, tensorHomVal_natAdd,
                Hom.id]

@[simp]
lemma braiding_naturality_right
    (X : CombinationalCircuit V G)
    {Y Z : CombinationalCircuit V G}
    (f : Y ⟶ Z) :
    MonoidalCategoryStruct.whiskerLeft X f ≫ (X.braiding Z).hom =
    (X.braiding Y).hom ≫ MonoidalCategoryStruct.whiskerRight f X := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp]
  have hwr : ∀ w, (MonoidalCategoryStruct.whiskerRight f X).val w = tensorHomVal f Hom.id w :=
    fun _ => rfl
  have hwl : ∀ w, (MonoidalCategoryStruct.whiskerLeft X f).val w = tensorHomVal Hom.id f w :=
    fun _ => rfl
  simp only [hwr, hwl]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [braiding_get_castAdd, tensorHomVal_castAdd, tensorHomVal_natAdd,
                Hom.id]
  · simp only [braiding_get_natAdd, tensorHomVal_castAdd, tensorHomVal_natAdd,
                Hom.id, Wires.get_ofFn]

@[simp]
lemma hexagon_forward
    (X Y Z : CombinationalCircuit V G) :
    (MonoidalCategoryStruct.associator X Y Z).hom ≫
      (X.braiding (MonoidalCategoryStruct.tensorObj Y Z)).hom ≫
      (MonoidalCategoryStruct.associator Y Z X).hom =
    MonoidalCategoryStruct.whiskerRight (X.braiding Y).hom Z ≫
      (MonoidalCategoryStruct.associator Y X Z).hom ≫
      MonoidalCategoryStruct.whiskerLeft Y (X.braiding Z).hom := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp]
  have hwr : ∀ w, (MonoidalCategoryStruct.whiskerRight (braiding X Y).hom Z).val w =
      tensorHomVal (braiding X Y).hom Hom.id w := fun _ => rfl
  have hwl : ∀ w, (MonoidalCategoryStruct.whiskerLeft Y (braiding X Z).hom).val w =
      tensorHomVal Hom.id (braiding X Z).hom w := fun _ => rfl
  simp only [hwr, hwl, associator_hom_val]
  have htobj : ∀ A B : CombinationalCircuit V G,
      (MonoidalCategoryStruct.tensorObj A B).obj = A.obj + B.obj := fun _ _ => rfl
  have hsub : ∀ a b : ℕ, a + b - a = b := by intros; omega
  refine Fin.addCases (fun j => ?_) (fun jj => Fin.addCases (fun k => ?_) (fun k => ?_) jj) i
  all_goals simp only [Fin.val_castAdd, Fin.val_natAdd, Wires.get_cast,
    braiding_get, tensorHomVal_get, tensorObj, htobj, hsub, Hom.id, Wires.get_ofFn]
  all_goals split_ifs <;> (first
    | (refine congrArg v.get (Fin.ext ?_); simp at *; done)
    | (refine congrArg v.get (Fin.ext ?_); simp; omega))

@[simp]
lemma hexagon_reverse
    (X Y Z : CombinationalCircuit V G) :
    (MonoidalCategoryStruct.associator X Y Z).inv ≫
      ((MonoidalCategoryStruct.tensorObj X Y).braiding Z).hom ≫
      (MonoidalCategoryStruct.associator Z X Y).inv =
    MonoidalCategoryStruct.whiskerLeft X (Y.braiding Z).hom ≫
      (MonoidalCategoryStruct.associator X Z Y).inv ≫
      MonoidalCategoryStruct.whiskerRight (X.braiding Z).hom Y := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp]
  have hwr : ∀ w, (MonoidalCategoryStruct.whiskerRight (braiding X Z).hom Y).val w =
      tensorHomVal (braiding X Z).hom Hom.id w := fun _ => rfl
  have hwl : ∀ w, (MonoidalCategoryStruct.whiskerLeft X (braiding Y Z).hom).val w =
      tensorHomVal Hom.id (braiding Y Z).hom w := fun _ => rfl
  simp only [hwr, hwl, associator_inv_val]
  have htobj : ∀ A B : CombinationalCircuit V G,
      (MonoidalCategoryStruct.tensorObj A B).obj = A.obj + B.obj := fun _ _ => rfl
  have hsub : ∀ a b : ℕ, a + b - a = b := by intros; omega
  refine Fin.addCases (fun jj => Fin.addCases (fun k => ?_) (fun k => ?_) jj) (fun j => ?_) i
  all_goals simp only [Fin.val_castAdd, Fin.val_natAdd, Wires.get_cast,
    braiding_get, tensorHomVal_get, tensorObj, htobj, hsub, Hom.id, Wires.get_ofFn]
  all_goals split_ifs <;> (first
    | (refine congrArg v.get (Fin.ext ?_); simp at *; done)
    | (refine congrArg v.get (Fin.ext ?_); simp [hsub]; omega))

@[simp]
lemma symmetry
    (X Y : CombinationalCircuit V G) :
    (X.braiding Y).hom ≫ (Y.braiding X).hom =
    𝟙 (MonoidalCategoryStruct.tensorObj X Y) := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp, CategoryStruct.id, Hom.id, braiding_get]
  split <;> split <;>
  exact congrArg v.get (Fin.ext (by simp only []; omega))

instance : SymmetricCategory (CombinationalCircuit V G) where
  braiding
  braiding_naturality_left
  braiding_naturality_right
  hexagon_forward
  hexagon_reverse
  symmetry

end CombinationalCircuit

end Circuit
