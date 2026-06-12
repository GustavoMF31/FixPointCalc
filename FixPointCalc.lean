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

-- Think: Simp tag this? (What about grind and cat_disch?)
lemma cata_comm (f : F.obj a ⟶ a)
  : F.map (cata h f) ≫ f = ι ≫ cata h f := (h.to _).h

lemma cata_unique (h : IsInitial (Algebra.mk μF ι))
  (f : F.obj a ⟶ a) (g₁ g₂ : μF ⟶ a)
  (h₁ : F.map g₁ ≫ f = ι ≫ g₁) (h₂ : F.map g₂ ≫ f = ι ≫ g₂) : g₁ = g₂ :=
  congr_arg Algebra.Hom.f (IsInitial.hom_ext (Y := ⟨a, f⟩) h ⟨g₁, h₁⟩ ⟨g₂, h₂⟩)

lemma cata_ext (f : F.obj a ⟶ a) (h₁ : F.map g ≫ f = ι ≫ g) : g = cata h f :=
    cata_unique h f _ _ h₁ (cata_comm h f)

lemma cata_ump (g : μF ⟶ a) (f : F.obj a ⟶ a) :
    g = cata h f ↔ F.map g ≫ f = ι ≫ g := by
      constructor
      · intro h₁; subst h₁
        apply cata_comm
      intro h₁
      apply cata_ext
      exact h₁

lemma cata_fusion (f : F.obj a ⟶ a) (g : a ⟶ b) (l : F.obj b ⟶ b)
    (h₁ : f ≫ g = F.map g ≫ l) : cata h f ≫ g = cata h l := by
      apply cata_ext
      rw [← Category.assoc ι, ← cata_comm, Functor.map_comp]
      rw [Category.assoc, ← h₁, ← Category.assoc]

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
    rw [← cata_comm, ← F.map_id, ← Functor.map_comp]
    apply congr_arg
    apply iota_inv h

end Catamorphism

-- TODO: Consider wrapping IsInitial to avoid Algebra and Algebra.mk
def rolling_rule
  (F : D ⥤ C) (G : C ⥤ D)
  -- {μFG : D} {ι₁ : (F ⋙ G).obj μFG ⟶ μFG}
  {μFG : D} {ι₁ : G.obj (F.obj μFG) ⟶ μFG}
  (h₁ : IsInitial (C := Algebra (F ⋙ G)) (Algebra.mk (F := F ⋙ G) μFG ι₁))
  : IsInitial (C := Algebra (G ⋙ F)) (Algebra.mk (F := G ⋙ F) (F.obj μFG) (F.map ι₁))
  := by
    refine IsInitial.ofUniqueHom ?_ ?_
    · intro ⟨a, f⟩
      simp at f
      refine Algebra.Hom.mk ?_ ?_
      · simp
        refine ?_ ≫ f
        apply F.map
        apply cata h₁
        simp
        apply G.map
        exact f
      · simp
        rw [← Category.assoc]
        rw [← Category.assoc]
        apply eq_whisker
        rw [← F.map_comp]
        rw [← F.map_comp]
        apply congr_arg
        have comm := cata_comm h₁ (G.map f)
        simp at comm
        exact comm
    · intro ⟨a, f⟩
      intro ⟨g, alg_comm⟩
      simp at f g alg_comm
      simp
      apply Algebra.Hom.ext
      simp

      let iso := lambek h₁
      simp at iso
      letI i : IsSplitEpi (F.map ι₁) := ⟨F.map iso.inv, by
        rw [← F.map_id, ← F.map_comp]
        apply congr_arg
        apply iso.inv_hom_id
        ⟩

      sorry
