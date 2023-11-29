import LeanCourse.Common
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic




/--Working with the assumption that S is a set of ordinals, this would give us the natural interpretation
when working with von Neumann ordinals in ZFC.-/
def unbounded_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  ( Ordinal.IsLimit o ) ∧ ( (∀ a : Ordinal, (a < o → ∃ b : Ordinal, b < o ∧ b ∈ C ∧ a < b)))

/-- Our definitions require interaction between sets and ordinals. We formulate this as
restricting a set of ordinals to the subset of elements smaller than a given ordinal.-/
def Ordinal_res (C : Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {c ∈ C | c ≤ o}

def sub_Ordinal (C : Set Ordinal) (o : Ordinal) : Prop :=
  Ordinal_res C o = C

lemma sub_Ordinal_iff_res_eq (C : Set Ordinal) (o : Ordinal) :
  sub_Ordinal C o ↔ (∀ c ∈ C, c ≤ o) := by
  {
    unfold sub_Ordinal ; unfold Ordinal_res
    exact Set.sep_eq_self_iff_mem_true
  }

def sub_unbounded_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  (unbounded_in (Ordinal_res C o) o)

def closed_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  (Ordinal.IsLimit o) ∧ (∀ a : Ordinal, (a < o ∧ sub_Ordinal C a) → sub_unbounded_in C a)

def sub_closed_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  closed_in (Ordinal_res C o) o

def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  sub_unbounded_in C o ∧ sub_closed_in C o

def stationary_in (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, (sub_Ordinal C o ∧ club_in C o) → S ∩ C ≠ ∅

lemma int_two_club (C D : Set Ordinal) (o : Ordinal) (hC: club_in C o) (hD : club_in D o) :
  club_in (C ∩ D) o := by
  {
    sorry
  }
