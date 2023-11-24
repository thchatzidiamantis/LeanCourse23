import LeanCourse.Common
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

universe u v w

variable {α : Type*} {r : α → α → Prop}

--Still trying to choose the right notion of a set being the subset of an ordinal

def unbounded (o : Ordinal) (S : Set α) : Prop :=
  ( Ordinal.IsLimit o ) ∧ ( (∀ a : Ordinal , ∃ b : Ordinal, b ∈ S, r a.r b))
