/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Circuitlib.Circuit.Category.Combinational
public import Mathlib.Data.Stream.Init

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

@[inline]
def Stream := Stream'

instance [Preorder α] : Preorder (Stream α) where
  le xs ys := (xs.zip (fun x y => (x, y)) ys).All ((fun (x, y) => x <= y))
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)

abbrev Stream.map.{u, v} {α : Type u} {β : Type v} : (α → β) → Stream α → Stream β := Stream'.map

universe u v

variable {V : Type v} {G : Type u}

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : SequentialCircuitCategory V G) :=
  { f : Stream (Wires V I.obj) → Stream (Wires V O.obj) // Monotone f }

@[inline, simp]
def id_val : Stream (Wires V n) → Stream (Wires V n) := fun x => x

variable [Preorder V]

@[simp]
lemma id_monotone : Monotone (id_val (V:=V) (n:=n)) := monotone_id

@[inline, simp]
def id : SequentialCircuitCategory.Hom V X X := ⟨id_val, id_monotone⟩

open CategoryTheory

@[inline, simp]
instance : Category.{v} (SequentialCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val, Monotone.comp g.property f.property⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[inline, simp]
abbrev tensorObj (X Y : SequentialCircuitCategory V G) : SequentialCircuitCategory V G :=
  .of V G (X.obj + Y.obj)

omit [Preorder V] in
@[simp]
lemma tensorHom_val_add
    {X₁ X₂ : SequentialCircuitCategory V G} :
    min X₁.obj (X₁.obj + X₂.obj) = X₁.obj := by simp

omit [Preorder V] in
@[simp]
lemma tensorHom_val_sub
    {X₁ X₂ : SequentialCircuitCategory V G} :
    X₁.obj + X₂.obj - X₁.obj = X₂.obj := by simp

@[inline, simp]
abbrev tensorHom_val
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Stream (Wires V (X₁.obj + X₂.obj))) :
    Stream (Wires V (Y₁.obj + Y₂.obj)) :=
  Stream'.zip (fun a b => a.append b)
    (f.val (Stream'.map (fun w => (w.take X₁.obj).cast tensorHom_val_add) v))
    (g.val (Stream'.map (fun w => (w.drop X₁.obj).cast tensorHom_val_sub) v))

omit [Preorder V] in
@[simp]
lemma tensorHom_take
    {X₁ X₂ : SequentialCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.take X₁.obj).cast tensorHom_val_add =
    Vector.ofFn fun i => a.get (Fin.castAdd X₂.obj i) := by
  apply Wires.ext; intro i
  simp [Vector.get]

@[inline, simp]
abbrev tensorHom_eq' {X₁ X₂ : SequentialCircuitCategory V G} (w : Vector V (X₁.obj + X₂.obj)) :=
  Vector.ofFn fun i ↦ Vector.get w (Fin.castAdd X₂.obj i)

@[simp]
lemma tensorHom_eq
    {X₁ Y₁ X₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (f : X₁ ⟶ Y₁)
    (t : ℕ) :
    (f.val (Stream'.map tensorHom_eq' v) t).toArray.size = Y₁.obj :=
  (f.val _ t).size_toArray

@[simp]
lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ) (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((tensorHom_val f g v).get t).get (Fin.castAdd Y₂.obj j) =
    (f.val (Stream'.map tensorHom_eq' v) t).get j := by
  have hsz := (f.val (Stream'.map (fun w =>
    Vector.ofFn fun i ↦ w.get (Fin.castAdd X₂.obj i)) v) t).size_toArray
  simp only [tensorHom_take, tensorHom_val, Stream'.get_zip,
    Vector.get, Vector.append]
  exact Array.getElem_append_left (by simp)

@[simp]
lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ) (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((tensorHom_val f g v).get t).get (Fin.natAdd Y₁.obj j) =
    (g.val (Stream'.map (fun w =>
      Vector.ofFn fun i ↦ Vector.get w (Fin.natAdd X₁.obj i)) v) t).get j := by
  have hdrop : ∀ (a : Wires V (X₁.obj + X₂.obj)),
      (a.drop X₁.obj).cast tensorHom_val_sub =
      Vector.ofFn fun i => a.get (Fin.natAdd X₁.obj i) := fun a => by
    apply Wires.ext; intro i
    simp [Vector.get, Vector.drop, Fin.val_natAdd]
  simp only [tensorHom_take, hdrop, tensorHom_val, Stream'.get_zip,
    Vector.get, Vector.append]
  rw [Array.getElem_append_right (by simp)]
  congr 1; simp

@[simp]
lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Monotone (tensorHom_val f g) := fun v₁ v₂ h t i =>
  Fin.addCases
    (fun j => by
      have lhs_eq := tensorHom_eq_left v₁ t j f g
      have rhs_eq := tensorHom_eq_left v₂ t j f g
      rw [lhs_eq, rhs_eq]
      exact f.property (fun t' k => by
        simp only [Stream'.get_map, Wires.get_ofFn]
        exact h t' (k.castAdd _)) t j)
    (fun j => by
      have lhs_eq := tensorHom_eq_right v₁ t j f g
      have rhs_eq := tensorHom_eq_right v₂ t j f g
      rw [lhs_eq, rhs_eq]
      exact g.property (fun t' k => by
        simp only [Stream'.get_map, Wires.get_ofFn]
        exact h t' (k.natAdd _)) t j)
    i

@[inline, simp]
abbrev tensorHom
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHom_val f g, tensorHom_monotone f g⟩

@[simp]
abbrev iso_hom_val (h : n = m) : Stream (Wires V n) → Stream (Wires V m) :=
  Stream'.map (·.cast h)

@[simp]
lemma iso_hom_monotone (h : n = m) : Monotone (iso_hom_val (V:=V) h) :=
  fun _ _ hab t i => hab t (i.cast h.symm)

@[simp]
abbrev iso_hom (h : n = m) : { f : Stream (Wires V n) → Stream (Wires V m) // Monotone f } :=
  ⟨iso_hom_val h, iso_hom_monotone h⟩

@[simp]
abbrev iso_inv_val (h : n = m) : Stream (Wires V m) → Stream (Wires V n) :=
  Stream'.map (·.cast h.symm)

@[simp]
lemma iso_inv_monotone (h : n = m) : Monotone (iso_inv_val (V:=V) h) :=
  fun _ _ hab t i => hab t (i.cast h)

@[simp]
abbrev iso_inv (h : n = m) : { f : Stream (Wires V m) → Stream (Wires V n) // Monotone f } :=
  ⟨iso_inv_val h, iso_inv_monotone h⟩

@[simp]
lemma iso_hom_inv_id
    (h : n = m) :
    iso_hom h ≫ iso_inv h = 𝟙 (OfNat.ofNat n : SequentialCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

@[simp]
lemma iso_inv_hom_id
    (h : n = m) :
    iso_inv h ≫ iso_hom h = 𝟙 (OfNat.ofNat m : SequentialCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

@[inline, simp]
def iso
    (h : n = m) :
    SequentialCircuitCategory.of V G n ≅ SequentialCircuitCategory.of V G m :=
  { hom := iso_hom h
    inv := iso_inv h
    hom_inv_id := iso_hom_inv_id h
    inv_hom_id := iso_inv_hom_id h }

@[simp]
lemma whisker
    (X Y : SequentialCircuitCategory V G) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext; funext v
  funext t
  change (tensorHom_val (𝟙 X) (𝟙 Y) v).get t = v.get t
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v t j (𝟙 X) (𝟙 Y)]
    simp [CategoryStruct.id, id, id_val, Stream'.map, Wires.get_ofFn]
  · rw [tensorHom_eq_right v t j (𝟙 X) (𝟙 Y)]
    simp [CategoryStruct.id, id, id_val, Stream'.map, Wires.get_ofFn]

@[inline, simp]
abbrev whiskerLeft
    (X : SequentialCircuitCategory V G)
    {Y₁ Y₂ : SequentialCircuitCategory V G} :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)

@[inline, simp]
abbrev whiskerRight
    {X₁ X₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ X₂)
    (Y : SequentialCircuitCategory V G) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

@[simp]
lemma tensorHom_def
    {W X Y Z : SequentialCircuitCategory V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ whiskerLeft X g := by
  apply Subtype.ext; funext v; funext t
  change (tensorHom_val f g v).get t =
    (tensorHom_val id g (tensorHom_val f id v)).get t
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v t j f g, tensorHom_eq_left _ t j id g]
    simp only [id, Stream'.map, id_val, Wires.get_ofFn]
    exact (tensorHom_eq_left v t j f id).symm
  · rw [tensorHom_eq_right v t j f g, tensorHom_eq_right _ t j id g]
    simp only [id]
    have heq : (Stream'.map (fun w =>
        Vector.ofFn fun i ↦ w.get (Fin.natAdd W.obj i)) v) =
      (Stream'.map (fun w =>
        Vector.ofFn fun i ↦ w.get (Fin.natAdd X.obj i))
          (tensorHom_val f ⟨id_val, id_monotone⟩ v)) := by
      funext t'; apply Wires.ext; intro k
      simp only [Stream'.map, Wires.get_ofFn]
      have := (tensorHom_eq_right v t' k f (𝟙 Y)).symm
      simp only [CategoryStruct.id, id, id_val, Stream'.map,
        Wires.get_ofFn] at this
      exact this
    exact congrArg (fun s => (g.val s t).get j) heq

@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : SequentialCircuitCategory V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := whisker X₁ X₂

@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SequentialCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext; funext v; funext t
  change (tensorHom_val g₁ g₂ (tensorHom_val f₁ f₂ v)).get t =
    (tensorHom_val (f₁ ≫ g₁) (f₂ ≫ g₂) v).get t
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ t j g₁ g₂,
        tensorHom_eq_left v t j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp, Function.comp]
    exact congrArg (fun s => (g₁.val s t).get j)
      (funext fun t' => Wires.ext fun k => by
        simp only [Stream'.map, Wires.get_ofFn]
        exact tensorHom_eq_left v t' k f₁ f₂)
  · rw [tensorHom_eq_right _ t j g₁ g₂,
        tensorHom_eq_right v t j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp, Function.comp]
    exact congrArg (fun s => (g₂.val s t).get j)
      (funext fun t' => Wires.ext fun k => by
        simp only [Stream'.map, Wires.get_ofFn]
        exact tensorHom_eq_right v t' k f₁ f₂)

@[inline, simp]
def tensorUnit : SequentialCircuitCategory V G := .of V G 0

omit [Preorder V] in
@[simp]
lemma associator_eq
    (X Y Z : SequentialCircuitCategory V G) :
    X.obj + Y.obj + Z.obj = X.obj + (Y.obj + Z.obj) :=
  Nat.add_assoc X.obj Y.obj Z.obj

@[inline, simp]
def associator
    (X Y Z : SequentialCircuitCategory V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  iso (associator_eq X Y Z)

@[simp]
lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SequentialCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext; funext v
  funext t; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp, tensorHom_val,
    associator, iso, iso_hom, iso_hom_val, Stream'.map_map,
    Stream'.map, Stream'.zip, Stream'.get, Vector.append,
    Vector.cast]
  simp only [Vector.getElem_mk, Array.append_assoc]
  congr 1; congr 1
  · exact congrArg Vector.toArray (congrFun (congrArg f₁.val
      (funext fun t' => Wires.ext fun k => by
        simp [Stream'.map, Function.comp, Vector.get, Vector.take])) t)
  congr 1
  · exact congrArg Vector.toArray (congrFun (congrArg f₂.val
      (funext fun t' => Wires.ext fun k => by
        simp [Stream'.map, Function.comp, Vector.get, Vector.take, Vector.drop])) t)
  · exact congrArg Vector.toArray (congrFun (congrArg f₃.val
      (funext fun t' => Wires.ext fun k => by
        simp [Stream'.map, Function.comp, Vector.get, Vector.drop])) t)

@[simp]
lemma pentagon
    (W X Y Z : SequentialCircuitCategory V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      whiskerLeft W (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext; funext v; funext t; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp, tensorHom_val,
    associator, iso, iso_hom, iso_hom_val,
    Vector.append, Vector.cast]
  unfold Stream'.map Stream'.zip Stream'.get
  simp [show W.obj + (X.obj + (Y.obj + Z.obj)) =
    W.obj + (X.obj + Y.obj) + Z.obj from by omega,
    show min W.obj (W.obj + (X.obj + Y.obj) + Z.obj) = W.obj from by omega]

omit [Preorder V] in
@[simp]
lemma leftUnitor_eq
    (X : SequentialCircuitCategory V G) :
    (tensorUnit (V:=V) (G:=G)).obj + X.obj = X.obj :=
  Nat.zero_add X.obj

omit [Preorder V] in
@[simp]
lemma rightUnitor_eq
    (X : SequentialCircuitCategory V G) :
    X.obj + (tensorUnit (V:=V) (G:=G)).obj = X.obj :=
  Nat.add_zero X.obj

@[simp]
abbrev leftUnitor (X : SequentialCircuitCategory V G) : tensorObj tensorUnit X ≅ X :=
  iso (leftUnitor_eq X)

@[simp]
abbrev rightUnitor (X : SequentialCircuitCategory V G) : tensorObj X tensorUnit ≅ X :=
  iso (rightUnitor_eq X)

@[simp]
lemma leftUnitor_naturality
    {X Y : SequentialCircuitCategory V G} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; funext t; apply Vector.ext; intro i hi
  simp only [iso, CategoryStruct.comp, Function.comp,
    tensorHom_val, iso_hom_val, iso_hom]
  unfold Stream'.map Stream'.zip Stream'.get
  simp [Vector.append]

@[simp]
lemma rightUnitor_naturality
    {X Y : SequentialCircuitCategory V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; funext t; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp,
    tensorHom_val, iso_hom_val, iso_hom, iso]
  unfold Stream'.map Stream'.zip Stream'.get
  have : (v t).toArray.extract X.obj X.obj = #[] := by grind
  simp [Vector.append, this]

open MonoidalCategory

@[simp]
lemma triangle
    (X Y : SequentialCircuitCategory V G) :
    (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
    whiskerRight (rightUnitor X).hom Y := by
  apply Subtype.ext; funext v; funext t; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp,
    tensorHom_val, iso_hom_val, iso_hom, iso]
  unfold Stream'.map Stream'.zip Stream'.get
  simp [Stream'.map, Stream'.get, Vector.cast]

@[inline, simp]
instance : MonoidalCategory.{v} (SequentialCircuitCategory V G) where
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
  leftUnitor
  leftUnitor_naturality
  rightUnitor
  rightUnitor_naturality
  pentagon
  triangle

end SequentialCircuitCategory

end Circuit
