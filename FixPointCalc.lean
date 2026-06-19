import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Basic
-- import Mathlib.CategoryTheory.NatTrans

import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

open CategoryTheory
open CategoryTheory.Endofunctor
open CategoryTheory.Limits

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

abbrev InitialAlgebra {a : C} (F : C ⥤ C) (f : F.obj a ⟶ a)
  := IsInitial (Algebra.mk a f)

section Catamorphism

variable {F : C ⥤ C} {μF : C} {ι : F.obj μF ⟶ μF}
variable (h : InitialAlgebra F ι)

def cata {a : C} (f : F.obj a ⟶ a) : μF ⟶ a := (h.to ⟨a, f⟩).f

-- TODO: Develop rules of thumb for when to tag things with grind
@[reassoc (attr := simp), grind =]
lemma cata_comm (f : F.obj a ⟶ a)
  : ι ≫ cata h f = F.map (cata h f) ≫ f := Eq.symm (h.to _).h

@[reassoc (attr := simp), grind =]
lemma cata_comm_map (G : C ⥤ D) (f : F.obj a ⟶ a)
  : G.map ι ≫ G.map (cata h f) = G.map (F.map (cata h f)) ≫ G.map f
  := by grind

lemma cata_unique (h : InitialAlgebra F ι)
  (f : F.obj a ⟶ a) (g₁ g₂ : μF ⟶ a)
  (h₁ : ι ≫ g₁ = F.map g₁ ≫ f) (h₂ : ι ≫ g₂ = F.map g₂ ≫ f) : g₁ = g₂ :=
  congr_arg Algebra.Hom.f
    (IsInitial.hom_ext (Y := ⟨a, f⟩) h ⟨g₁, Eq.symm h₁⟩ ⟨g₂, Eq.symm h₂⟩)

lemma cata_ext (f : F.obj a ⟶ a) (h₁ : ι ≫ g = F.map g ≫ f) : g = cata h f :=
    cata_unique h f _ _ h₁ (cata_comm h f)

lemma cata_ump (g : μF ⟶ a) (f : F.obj a ⟶ a) :
    g = cata h f ↔ ι ≫ g = F.map g ≫ f := by grind [cata_ext]

lemma cata_fusion (f : F.obj a ⟶ a) (g : a ⟶ b) (l : F.obj b ⟶ b)
    (h₁ : f ≫ g = F.map g ≫ l) : cata h f ≫ g = cata h l := by
      apply cata_ext
      rw [← Category.assoc ι, cata_comm, Functor.map_comp]
      rw [Category.assoc, h₁, ← Category.assoc]

lemma cata_iota_id : cata h ι = 𝟙 μF := by
  apply symm; apply cata_ext; aesop_cat

-- This could be taken as a direct corollary of the fact that initial objects
-- are unique, but defining the isomorphism directly in terms of catamorphisms
-- allows us to use catamorphism rules later on.
def init_alg_uniq (f : F.obj a ⟶ a) (g : F.obj b ⟶ b)
    (h₁ : InitialAlgebra F f)
    (h₂ : InitialAlgebra F g) : a ≅ b where
      hom := cata h₁ g
      inv := cata h₂ f
      inv_hom_id := by rw [← cata_iota_id h₂]; apply cata_fusion; aesop_cat
      hom_inv_id := by rw [← cata_iota_id h₁]; apply cata_fusion; aesop_cat

lemma iota_inv : cata h (F.map ι) ≫ ι = 𝟙 μF := by
  rw [← cata_iota_id h]
  apply cata_fusion
  rfl

-- TODO: Show that F ι is also initial in the category of algebras,
-- and get an isomorphism from there. Then simplify it to the one below.
def lambek : F.obj μF ≅ μF where
  hom := ι
  inv := cata h (F.map ι)
  inv_hom_id := iota_inv h
  hom_inv_id := by
    rw [cata_comm, ← F.map_id, ← Functor.map_comp]
    apply congr_arg
    apply iota_inv h

-- Every endofunctor extends to an endofunctor on its category of algebras
-- TODO: This construction is really the (contravariant?) functorial action of
-- Algebra : Cat^op -> Cat
def map_alg (F : C ⥤ C) : Algebra F ⥤ Algebra F where
  obj alg := ⟨F.obj alg.a, F.map alg.str⟩
  map alg_hom := Algebra.Hom.mk (F.map alg_hom.f) (by
    simp only [← F.map_comp]
    aesop_cat
  )

-- Lemma 19.17: Every F-algebra induces a corresponding F-algebra morphism
def asMorphism (f : Algebra F) : (map_alg F).obj f ⟶ f := Algebra.Hom.mk f.str

def Sq : Algebra F ⥤ Algebra (F ⋙ F) where
  obj alg := Algebra.mk alg.a (F.map alg.str ≫ alg.str)
  map alg_hom := Algebra.Hom.mk alg_hom.f (by
    simp only [Functor.comp_obj, Functor.comp_map, Category.assoc]
    rw [← alg_hom.h, ← Category.assoc, ← F.map_comp, ← Category.assoc]
    simp
  )

end Catamorphism

set_option backward.isDefEq.respectTransparency false in
def rolling_rule
  (F : D ⥤ C) (G : C ⥤ D)
  {μFG : D} {ι₁ : (F ⋙ G).obj μFG ⟶ μFG}
  (h₁ : InitialAlgebra (F ⋙ G) ι₁)
  : InitialAlgebra (G ⋙ F) (F.map ι₁)
  := by
    apply IsInitial.ofUniqueHom (fun ⟨a, f⟩ ↦
        Algebra.Hom.mk ((F.map (cata h₁ (G.map f))) ≫ f))
    intro ⟨a, f⟩ ⟨g, alg_comm⟩
    simp only [Functor.comp_map] at alg_comm
    apply Algebra.Hom.ext
    rw [← Iso.cancel_iso_hom_left (F.mapIso (lambek h₁))]
    unfold lambek
    simp only [Functor.comp_obj, Functor.comp_map, Functor.mapIso_hom]
    rw [← alg_comm, ← Category.assoc]
    apply eq_whisker
    rw [← F.map_comp]
    apply congr_arg
    erw [← Iso.inv_comp_eq (lambek h₁)]
    apply cata_fusion
    simp [← Functor.map_comp, alg_comm]

def rolling_rule_iso
  (F : D ⥤ C) (G : C ⥤ D)
  {μFG : D} {ι₁ : (F ⋙ G).obj μFG ⟶ μFG}
  {μGF : C} {ι₂ : (G ⋙ F).obj μGF ⟶ μGF}
  (h₁ : InitialAlgebra (F ⋙ G) ι₁)
  (h₂ : InitialAlgebra (G ⋙ F) ι₂)
  : μFG ≅ G.obj μGF
  := init_alg_uniq ι₁ (G.map ι₂) h₁ (rolling_rule G F h₂)

set_option backward.isDefEq.respectTransparency false in
def square_rule
  (F : C ⥤ C)
  {μFF : C} {ι : (F ⋙ F).obj μFF ⟶ μFF}
  (h : InitialAlgebra (F ⋙ F) ι)
  : InitialAlgebra F (F.map (cata h (F.map ι)) ≫ ι) := by

  apply IsInitial.ofUniqueHom (fun ⟨_, f⟩ =>
    Algebra.Hom.mk (cata h (F.map f ≫ f)) (by 
      simp only [Functor.comp_obj, Category.assoc, cata_comm, Functor.comp_map]
      simp only [← Category.assoc]
      apply eq_whisker
      simp only [Category.assoc]
      simp only [← Functor.map_comp]
      apply congr_arg
      apply Eq.symm
      apply cata_fusion
      simp [← Category.assoc]
    ))
  intro ⟨a, f⟩ ⟨g, alg_comm⟩
  simp
  apply Algebra.Hom.ext
  simp
  apply cata_ext
  simp at *
  simp at g
  rw [← Category.assoc, ← F.map_comp, alg_comm]
  simp
  sorry

