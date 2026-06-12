import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
-- import Mathlib.CategoryTheory.NatTrans

import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

open CategoryTheory
open CategoryTheory.Endofunctor

section

variable {C : Type u} [Category.{v} C]
variable {F : C ⥤ C}
variable {μF : C} {ι : F.obj μF ⟶ μF}
variable (h : Limits.IsInitial (Algebra.mk μF ι))

-- Think: Every endofunctor lifts to an endofunctor on its category of algebras
-- Think: The category of F-algebras construction is functorial

def cata {a : C} (f : F.obj a ⟶ a) : μF ⟶ a := (h.to ⟨a, f⟩).f

-- Think: Simp tag this? (What about grind and cat_disch?)
lemma cata_comm (f : F.obj a ⟶ a) : F.map (cata h f) ≫ f = ι ≫ cata h f := (h.to _).h

lemma cata_unique (h : Limits.IsInitial (Algebra.mk μF ι))
  (f : F.obj a ⟶ a) (g₁ g₂ : μF ⟶ a)
  (h₁ : F.map g₁ ≫ f = ι ≫ g₁) (h₂ : F.map g₂ ≫ f = ι ≫ g₂) : g₁ = g₂ :=
  congr_arg Algebra.Hom.f (Limits.IsInitial.hom_ext (Y := ⟨a, f⟩) h ⟨g₁, h₁⟩ ⟨g₂, h₂⟩)

lemma cata_ump (g : μF ⟶ a) (f : F.obj a ⟶ a) :
    g = cata h f ↔ F.map g ≫ f = ι ≫ g := by
      constructor
      · intro h₁; subst h₁
        apply cata_comm
      intro h₁
      apply cata_unique h
      · exact h₁
      · apply cata_comm

-- cata h (F.map ι) ≫ ι = 𝟙 μF := by
lemma str_inv (F : C ⥤ C) (A : Algebra F) (h : Limits.IsInitial A) :
  (h.to { a := F.obj A.a, str := F.map A.str }).f ≫ A.str = 𝟙 A.a := by
      let alg_id : A ⟶ A := ⟨𝟙 A.a, by cat_disch⟩
      let alg_hom : A ⟶ A
        := ⟨(h.to { a := F.obj A.a, str := F.map A.str }).f ≫ A.str,
        by
          rw [← Category.assoc]
          rw [← ((h.to { a := F.obj A.a, str := F.map A.str }).h)]
          cat_disch
      ⟩
      change alg_hom.f = alg_id.f
      rw [← Endofunctor.Algebra.Hom.ext_iff]
      apply Limits.IsInitial.hom_ext h

-- F muF = muF
def lambek (F : C ⥤ C) (A : Algebra F) (h : Limits.IsInitial A) :
  F.obj A.a ≅ A.a where
    hom := A.str
    inv := (h.to ⟨F.obj A.a , F.map A.str⟩).f
    hom_inv_id := by
      rw [← (h.to ⟨F.obj A.a , F.map A.str⟩).h]
      simp only
      rw [← F.map_id, ← F.map_comp]
      apply congr_arg
      apply str_inv

    inv_hom_id := by apply str_inv

end
