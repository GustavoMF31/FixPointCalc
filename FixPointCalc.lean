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

-- TODO: Rename this h to a more reasonable letter
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

-- cata h (F.map ι) ≫ ι = 𝟙 μF := by
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

end
