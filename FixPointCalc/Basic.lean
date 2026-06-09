import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
-- import Mathlib.CategoryTheory.NatTrans

import Mathlib.CategoryTheory.Endofunctor.Algebra

open CategoryTheory
open CategoryTheory.Endofunctor

-- TODO: Think about universes

section

variable {C : Type u} [Category.{v} C]

-- Think: Every endofunctor lifts to an endofunctor on its category of algebras
-- Think: The category of F-algebras construction is functorial

-- F muF = muF
def lambek (F : C ⥤ C) (A : Algebra F) (h : Limits.IsInitial A) :
  F.obj A.a ≅ A.a where
    hom := A.str
    inv := (h.to ⟨F.obj A.a , F.map A.str⟩).f
    hom_inv_id := _
    inv_hom_id := by
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


end
