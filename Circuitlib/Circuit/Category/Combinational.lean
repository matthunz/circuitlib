/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import Circuitlib.Circuit.Category.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-! # Combinational circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- Category of combinational circuits. -/
structure CombinationalCircuitCategory (V : Type*) (G : Type*) where of (V) (G) ::
  obj : ℕ

attribute [inline, simp] CombinationalCircuitCategory.obj

@[simp]
instance : OfNat (CombinationalCircuitCategory V G) n where
  ofNat := .of V G n

namespace CombinationalCircuitCategory

universe u v

variable {V : Type v} {G : Type u}

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : CombinationalCircuitCategory V G) :=
  { f : Wires V I.obj → Wires V O.obj // Monotone f }

@[inline, simp]
abbrev id_val : Wires V n → Wires V n := fun x => x

@[simp]
lemma id_monotone [Preorder V] : Monotone (id_val (V:=V) (n:=n)) := monotone_id

@[inline, simp]
def id [Preorder V] : CombinationalCircuitCategory.Hom V X X := ⟨id_val, id_monotone⟩

open CategoryTheory

@[inline, simp]
instance [Preorder V] : Category.{v} (CombinationalCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val, Monotone.comp g.property f.property⟩
  id_comp _ := by rfl
  comp_id _ := by rfl
  assoc _ _ _ := by rfl

@[inline, simp]
def drop (_ : Wires V 1) : Wires V 0 := #v[]

@[simp]
lemma drop_monotone [Preorder V] : Monotone (drop (V:=V)) := fun _ _ _ => le_refl _

@[inline, simp]
abbrev fork (w : Wires V 1) : Wires V 2 := #v[w.get 0, w.get 0]

@[simp]
lemma fork_monotone [Preorder V] : Monotone (fork (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> exact h 0

@[inline, simp]
def join [SemilatticeSup V] (w : Wires V 2) : Wires V 1 := #v[w.get 0 ⊔ w.get 1]

@[simp]
lemma join_monotone [SemilatticeSup V] : Monotone (join (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 := by omega
  subst this; exact sup_le_sup (h 0) (h 1)

@[inline, simp]
abbrev tensorObj (X Y : CombinationalCircuitCategory V G) : CombinationalCircuitCategory V G :=
  .of V G (X.obj + Y.obj)

variable [SemilatticeSup V]

@[inline, simp]
instance [Gate V G] [Bot V] : CircuitCategory V G (CombinationalCircuitCategory V G) where
  gate g := ⟨Gate.gate g, Gate.gate_monotone g⟩
  stub := ⟨fun _ => #v[⊥], fun _ _ _ => le_refl _⟩
  drop := ⟨drop, drop_monotone⟩
  fork := ⟨fork, fork_monotone⟩
  join := ⟨join, join_monotone⟩

@[inline, simp]
abbrev tensorHom_val
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Wires V (X₁.obj + X₂.obj)) :
    Wires V (Y₁.obj + Y₂.obj) :=
  (f.val (Vector.ofFn (fun i => v.get (i.castAdd _)))).append
    (g.val (Vector.ofFn (fun i => v.get (i.natAdd _))))

@[simp]
lemma tensorHom_eq
    {X₁ Y₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (f : X₁ ⟶ Y₁) :
    (f.val (Vector.ofFn fun i ↦ Vector.get a (Fin.castAdd X₂.obj i))).toArray.size = Y₁.obj :=
  (f.val (Vector.ofFn (fun i => a.get (i.castAdd _)))).size_toArray

@[simp]
lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHom_val f g a).get (Fin.castAdd Y₂.obj j) =
    Vector.get (f.val (Vector.ofFn fun i => Vector.get a (Fin.castAdd X₂.obj i))) j := by
  have hf := tensorHom_eq a f
  simp only [Vector.get, Vector.append, Fin.val_cast, Fin.val_castAdd] at hf ⊢
  exact Array.getElem_append_left (by omega)

@[simp]
lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHom_val f g a).get (Fin.natAdd Y₁.obj j) =
    Vector.get (g.val (Vector.ofFn fun i => Vector.get a (Fin.natAdd X₁.obj i))) j := by
  have hf := tensorHom_eq a f
  simp only [Vector.get, Vector.append, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] at hf ⊢
  rw [Array.getElem_append_right (by omega)]
  congr 1; omega

@[simp]
lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Monotone (tensorHom_val f g) := fun a b h i =>
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

@[inline, simp]
abbrev tensorHom
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHom_val f g, tensorHom_monotone f g⟩

@[simp]
abbrev iso_hom_val (h : n = m) : Wires V n → Wires V m := (·.cast h)

@[simp]
lemma iso_hom_monotone (h : n = m) : Monotone (iso_hom_val (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h.symm)

@[simp]
abbrev iso_hom (h : n = m) : { f : Wires V n → Wires V m // Monotone f } :=
  ⟨iso_hom_val h, iso_hom_monotone h⟩

@[simp]
abbrev iso_inv_val (h : n = m) : Wires V m → Wires V n := (·.cast h.symm)

@[simp]
lemma iso_inv_monotone (h : n = m) : Monotone (iso_inv_val (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h)

@[simp]
abbrev iso_inv (h : n = m) : { f : Wires V m → Wires V n // Monotone f } :=
  ⟨iso_inv_val h, iso_inv_monotone h⟩

@[simp]
lemma iso_hom_inv_id
    (h : n = m) :
    iso_hom h ≫ iso_inv h = 𝟙 (OfNat.ofNat n : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

@[simp]
lemma iso_inv_hom_id
    (h : n = m) :
    iso_inv h ≫ iso_hom h = 𝟙 (OfNat.ofNat m : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

@[inline, simp]
abbrev iso
    (h : n = m) :
    CombinationalCircuitCategory.of V G n ≅ CombinationalCircuitCategory.of V G m :=
  { hom := iso_hom h
    inv := iso_inv h
    hom_inv_id := iso_hom_inv_id h
    inv_hom_id := iso_inv_hom_id h }

@[simp]
lemma whisker
    (X Y : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext; funext v
  change tensorHom_val (𝟙 X) (𝟙 Y) v = v
  unfold tensorHom_val
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id]; rw [Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id]; rw [Wires.get_ofFn]

@[inline, simp]
abbrev whiskerLeft
    (X : CombinationalCircuitCategory V G)
    {Y₁ Y₂ : CombinationalCircuitCategory V G} :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)

@[inline, simp]
abbrev whiskerRight
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ X₂)
    (Y : CombinationalCircuitCategory V G) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

@[simp]
lemma tensorHom_def
    {W X Y Z : CombinationalCircuitCategory V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ whiskerLeft X g := by
  apply Subtype.ext; funext v
  change tensorHom_val f g v = tensorHom_val id g (tensorHom_val f id v)
  unfold tensorHom_val
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j f g, tensorHom_eq_left _ j id g]
    simp only [id]; rw [Wires.get_ofFn]
    exact (tensorHom_eq_left v j f id).symm
  · rw [tensorHom_eq_right v j f g, tensorHom_eq_right _ j id g]
    simp only [id]
    exact congrArg (fun x => (g.val x).get j)
      (Wires.ext (fun k => by
        conv_rhs => rw [Wires.get_ofFn]
        exact (tensorHom_eq_right v k f (𝟙 _)).symm))

@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := by
  apply Subtype.ext; funext v
  change tensorHom_val (𝟙 X₁) (𝟙 X₂) v = v
  unfold tensorHom_val
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id]; rw [Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id]; rw [Wires.get_ofFn]

@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext; funext v
  change tensorHom_val g₁ g₂ (tensorHom_val f₁ f₂ v) = tensorHom_val (f₁ ≫ g₁) (f₂ ≫ g₂) v
  unfold tensorHom_val
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ j g₁ g₂, tensorHom_eq_left v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₁.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_left v k f₁ f₂))
  · rw [tensorHom_eq_right _ j g₁ g₂, tensorHom_eq_right v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₂.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_right v k f₁ f₂))

@[simp]
abbrev tensorUnit : CombinationalCircuitCategory V G := .of V G 0

omit [SemilatticeSup V] in
@[simp]
lemma associator_eq
    (X Y Z : CombinationalCircuitCategory V G) :
    X.obj + Y.obj + Z.obj = X.obj + (Y.obj + Z.obj) :=
  Nat.add_assoc X.obj Y.obj Z.obj

@[inline, simp]
abbrev associator
    (X Y Z : CombinationalCircuitCategory V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  iso (associator_eq X Y Z)

@[simp]
lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [Vector.get, CategoryStruct.comp, tensorHom_val, tensorHom,
              Vector.cast, Vector.append, Vector.toArray_ofFn, Array.getElem_ofFn,
              Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast, Function.comp,
              Array.append_assoc]
  simp only [show (X₁ + X₂).obj = X₁.obj + X₂.obj from rfl, Nat.add_assoc]

@[simp]
lemma pentagon
    (W X Y Z : CombinationalCircuitCategory V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      whiskerLeft W (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [id, CategoryStruct.id, tensorHom_val, tensorObj, Vector.get, CategoryStruct.comp,
             Vector.cast, Vector.append, Vector.toArray_ofFn, Fin.val_castAdd, Fin.val_natAdd,
             Fin.val_cast, Function.comp]
  have vec_arr : ∀ {n} (v : Vector V n) (j : Nat) (hj : j < n),
      v[j] = v.toArray[j]'(by rw [v.size_toArray]; exact hj) := fun _ _ _ => rfl
  simp only [vec_arr]
  have hWXY : (W.obj + X.obj + Y.obj) =
      W.obj + X.obj + Y.obj := rfl
  have hXYZ : (X.obj + (Y.obj + Z.obj)) =
      X.obj + (Y.obj + Z.obj) := rfl
  have hN : (CombinationalCircuitCategory.of V G (W.obj + (X.obj + (Y.obj + Z.obj)))).obj =
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

omit [SemilatticeSup V] in
@[simp]
lemma leftUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    (tensorUnit (V:=V) (G:=G)).obj + X.obj = X.obj :=
  Nat.zero_add X.obj

omit [SemilatticeSup V] in
@[simp]
lemma rightUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    X.obj + (tensorUnit (V:=V) (G:=G)).obj = X.obj :=
  Nat.add_zero X.obj

@[simp]
abbrev leftUnitor (X : CombinationalCircuitCategory V G) : tensorObj tensorUnit X ≅ X :=
  iso (leftUnitor_eq X)

@[simp]
abbrev rightUnitor (X : CombinationalCircuitCategory V G) : tensorObj X tensorUnit ≅ X :=
  iso (rightUnitor_eq X)

@[simp]
lemma leftUnitor_naturality
    {X Y : CombinationalCircuitCategory V G} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp]
  simp only [id, CategoryStruct.id, tensorUnit, Vector.get, tensorHom_val,
            Vector.append, Vector.toArray_ofFn, Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast]
  simp only [Vector.getElem_toArray, Array.ofFn_zero, Array.empty_append]
  exact congrArg (fun x => (f.val x).get ⟨i, hi⟩)
    (by apply Vector.ext; intro j hj; simp)

@[simp]
lemma rightUnitor_naturality
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp]
  simp only [id, CategoryStruct.id, tensorUnit, Vector.get, tensorHom_val,
              Vector.append, Vector.toArray_ofFn,
              Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast, Nat.add_zero]
  simp only [Vector.getElem_toArray, Array.ofFn_zero, Array.append_empty, Vector.mk_toArray]
  exact congrArg (fun x => (f.val x).get ⟨i, hi⟩)
    (by apply Vector.ext; intro j hj; simp)

open MonoidalCategory

@[simp]
lemma triangle
    (X Y : CombinationalCircuitCategory V G) :
    (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
    whiskerRight (rightUnitor X).hom Y := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [id, CategoryStruct.id, tensorObj, Vector.get, CategoryStruct.comp, tensorHom_val,
             Vector.cast, Vector.append, Vector.toArray_ofFn, Fin.val_castAdd, Fin.val_natAdd,
             Fin.val_cast, Function.comp]
  have vec_arr : ∀ {n} (v : Vector V n) (j : Nat) (hj : j < n),
      v[j] = v.toArray[j]'(by rw [v.size_toArray]; exact hj) := fun _ _ _ => rfl
  simp only [vec_arr]
  have h0 : (CombinationalCircuitCategory.of V G 0).obj = 0 := rfl
  have hX0 : (X.obj + ((CombinationalCircuitCategory.of V G 0).obj)) = X.obj + 0 := rfl
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

@[inline, simp]
instance : MonoidalCategory.{v} (CombinationalCircuitCategory V G) where
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

@[inline, simp]
def braiding_hom (X Y : CombinationalCircuitCategory V G) : tensorObj X Y ⟶ tensorObj Y X :=
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
    {X Y : CombinationalCircuitCategory V G} :
    X.braiding_hom Y ≫ Y.braiding_hom X = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, CategoryStruct.id, id,
             braiding_hom, Wires.get_ofFn]
  split <;> split <;>
    first | (simp only [] at *; omega)
          | exact congrArg v.get (Fin.ext (by simp only []; omega))

@[inline, simp]
def braiding (X Y : CombinationalCircuitCategory V G) : tensorObj X Y ≅ tensorObj Y X :=
  { hom := braiding_hom X Y
    inv := braiding_hom Y X
    hom_inv_id
    inv_hom_id := hom_inv_id }

@[simp]
lemma braiding_get
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj))
    (i : Fin (Y.obj + X.obj)) :
    ((braiding X Y).hom.val v).get i =
      if h : i.val < Y.obj
      then v.get ⟨X.obj + i.val, by omega⟩
      else v.get ⟨i.val - Y.obj, by omega⟩ := by
  unfold braiding braiding_hom; simp only [Wires.get_ofFn]

@[simp]
lemma braiding_get_castAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin Y.obj) :
    ((braiding X Y).hom.val v).get (Fin.castAdd X.obj j) =
    v.get (Fin.natAdd X.obj j) := by
  simp only [braiding_get, Fin.val_castAdd, dif_pos j.isLt]
  exact congrArg v.get (Fin.ext (by simp [Fin.val_natAdd]))

@[simp]
lemma braiding_get_natAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin X.obj) :
    ((braiding X Y).hom.val v).get (Fin.natAdd Y.obj j) =
    v.get (Fin.castAdd Y.obj j) := by
  simp only [braiding_get, Fin.val_natAdd,
             dif_neg (show ¬(Y.obj + j.val < Y.obj) from by omega)]
  exact congrArg v.get (Fin.ext (by simp [Fin.val_castAdd]))

@[simp]
lemma tensorHomVal_get
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (w : Wires V (X₁.obj + X₂.obj))
    (i : Fin (Y₁.obj + Y₂.obj)) :
    (tensorHom_val f g w).get i =
    if h : i.val < Y₁.obj
    then (f.val (Vector.ofFn fun k => w.get (Fin.castAdd X₂.obj k))).get ⟨i.val, h⟩
    else (g.val (Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k))).get
      ⟨i.val - Y₁.obj, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tensorHom_eq_left, Fin.val_castAdd, dif_pos j.isLt]
  · simp only [tensorHom_eq_right, Fin.val_natAdd,
               dif_neg (show ¬(Y₁.obj + j.val < Y₁.obj) from by omega)]
    congr 1; exact Fin.ext (by simp)

@[simp]
lemma braiding_naturality_left
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y)
    (Z : CombinationalCircuitCategory V G) :
    whiskerRight f Z ≫ (Y.braiding Z).hom =
    (braiding X Z).hom ≫ whiskerLeft Z f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [braiding_get_castAdd, tensorHom_eq_left, tensorHom_eq_right]
  · simp only [braiding_get_natAdd, tensorHom_eq_left, tensorHom_eq_right]

@[simp]
lemma braiding_naturality_right
    (X : CombinationalCircuitCategory V G)
    {Y Z : CombinationalCircuitCategory V G}
    (f : Y ⟶ Z) :
    whiskerLeft X f ≫ (X.braiding Z).hom =
    (braiding X Y).hom ≫ whiskerRight f X := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [braiding_get_castAdd, tensorHom_eq_left, tensorHom_eq_right]
  · simp only [braiding_get_natAdd, tensorHom_eq_left, tensorHom_eq_right]

@[simp]
lemma hexagon_forward
    (X Y Z : CombinationalCircuitCategory V G) :
    (associator X Y Z).hom ≫
      (X.braiding (tensorObj Y Z)).hom ≫
      (associator Y Z X).hom =
    whiskerRight (X.braiding Y).hom Z ≫
      (associator Y X Z).hom ≫
      whiskerLeft Y (X.braiding Z).hom := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [id, CategoryStruct.id, CategoryStruct.comp, Function.comp]
  have hsub : ∀ a b : ℕ, a + b - a = b := by intros; omega
  refine Fin.addCases (fun j => ?_) (fun jj => Fin.addCases (fun k => ?_) (fun k => ?_) jj) i
  all_goals simp only [Fin.val_castAdd, Fin.val_natAdd, Wires.get_cast,
    braiding_get, tensorHomVal_get, tensorObj, hsub, Wires.get_ofFn]
  all_goals split_ifs <;> (first
    | (refine congrArg v.get (Fin.ext ?_); simp at *; done)
    | (refine congrArg v.get (Fin.ext ?_); simp; omega))

@[simp]
lemma hexagon_reverse
    (X Y Z : CombinationalCircuitCategory V G) :
    (associator X Y Z).inv ≫
      ((tensorObj X Y).braiding Z).hom ≫
      (associator Z X Y).inv =
    whiskerLeft X (Y.braiding Z).hom ≫
      (associator X Z Y).inv ≫
      whiskerRight (X.braiding Z).hom Y := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [id, CategoryStruct.id, CategoryStruct.comp, Function.comp]
  have hsub : ∀ a b : ℕ, a + b - a = b := by intros; omega
  refine Fin.addCases (fun jj => Fin.addCases (fun k => ?_) (fun k => ?_) jj) (fun j => ?_) i
  all_goals simp only [Fin.val_castAdd, Fin.val_natAdd, Wires.get_cast,
    braiding_get, tensorHomVal_get, tensorObj, hsub, Wires.get_ofFn]
  all_goals split_ifs <;> (first
    | (refine congrArg v.get (Fin.ext ?_); simp at *; done)
    | (refine congrArg v.get (Fin.ext ?_); simp [hsub]; omega))

@[simp]
lemma symmetry
    (X Y : CombinationalCircuitCategory V G) :
    (X.braiding Y).hom ≫ (Y.braiding X).hom =
    𝟙 (tensorObj X Y) := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp, CategoryStruct.id, id, braiding_get]
  split <;> split <;>
  exact congrArg v.get (Fin.ext (by simp only []; omega))

@[simp]
instance : SymmetricCategory (CombinationalCircuitCategory V G) where
  braiding
  braiding_naturality_left
  braiding_naturality_right
  hexagon_forward
  hexagon_reverse
  symmetry

end CombinationalCircuitCategory

end Circuit
