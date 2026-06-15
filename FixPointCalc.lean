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

section Catamorphism

variable {F : C ⥤ C} {μF : C} {ι : F.obj μF ⟶ μF}

-- TODO: Rename this h to a more reasonable letter
variable (h : IsInitial (Algebra.mk μF ι))

def cata {a : C} (f : F.obj a ⟶ a) : μF ⟶ a := (h.to ⟨a, f⟩).f

@[reassoc (attr := simp), grind =]
lemma cata_comm (f : F.obj a ⟶ a)
  : ι ≫ cata h f = F.map (cata h f) ≫ f := Eq.symm (h.to _).h

@[reassoc (attr := simp)]
lemma cata_comm_map (G : C ⥤ D) (f : F.obj a ⟶ a)
  : G.map ι ≫ G.map (cata h f) = G.map (F.map (cata h f)) ≫ G.map f
  := by grind

lemma cata_unique (h : IsInitial (Algebra.mk μF ι))
  (f : F.obj a ⟶ a) (g₁ g₂ : μF ⟶ a)
  (h₁ : ι ≫ g₁ = F.map g₁ ≫ f) (h₂ : ι ≫ g₂ = F.map g₂ ≫ f) : g₁ = g₂ :=
  congr_arg Algebra.Hom.f
    (IsInitial.hom_ext (Y := ⟨a, f⟩) h ⟨g₁, Eq.symm h₁⟩ ⟨g₂, Eq.symm h₂⟩)

lemma cata_ext (f : F.obj a ⟶ a) (h₁ : ι ≫ g = F.map g ≫ f) : g = cata h f :=
    cata_unique h f _ _ h₁ (cata_comm h f)

-- TODO: There should be high-level tactic for accomplishing this proof here
lemma cata_ump (g : μF ⟶ a) (f : F.obj a ⟶ a) :
    g = cata h f ↔ ι ≫ g = F.map g ≫ f := by
      constructor
      · intro h₁; subst h₁
        apply cata_comm
      intro h₁
      apply cata_ext
      exact h₁

lemma cata_fusion (f : F.obj a ⟶ a) (g : a ⟶ b) (l : F.obj b ⟶ b)
    (h₁ : f ≫ g = F.map g ≫ l) : cata h f ≫ g = cata h l := by
      apply cata_ext
      rw [← Category.assoc ι, cata_comm, Functor.map_comp]
      rw [Category.assoc, h₁, ← Category.assoc]

lemma cata_iota_id : cata h ι = 𝟙 μF := by
  apply symm; apply cata_ext; cat_disch

lemma iota_inv : cata h (F.map ι) ≫ ι = 𝟙 μF := by
  rw [← cata_iota_id h]
  apply cata_fusion
  rfl

def lambek : F.obj μF ≅ μF where
  hom := ι
  inv := cata h (F.map ι)
  inv_hom_id := iota_inv h
  hom_inv_id := by
    rw [cata_comm, ← F.map_id, ← Functor.map_comp]
    apply congr_arg
    apply iota_inv h

end Catamorphism

-- TODO: Consider wrapping IsInitial to avoid Algebra and Algebra.mk
set_option backward.isDefEq.respectTransparency false in
def rolling_rule
  (F : D ⥤ C) (G : C ⥤ D)
  {μFG : D} {ι₁ : (F ⋙ G).obj μFG ⟶ μFG}
  (h₁ : IsInitial (Algebra.mk μFG ι₁))
  : IsInitial (Algebra.mk (F := G ⋙ F) (F.obj μFG) (F.map ι₁))
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
