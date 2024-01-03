import LeanCourse.Common
import Mathlib.Logic.Nonempty
import Mathlib.Init.Classical
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic


def Ordinal_int_nonempty {ι : Type} (C D : ι → Ordinal) : Prop := ∃ i j : ι, C i = D j

def Ordinal_mem (c : Ordinal) {ι : Type} (C : ι → Ordinal) :  Prop := ∃ i : ι, C i = c

def unbounded_in {ι : Type} (C : ι → Ordinal) (o : Ordinal) : Prop :=
  ( Ordinal.IsLimit o ) ∧ ( (∀ a : Ordinal, (a < o → ∃ i : ι, C i < o ∧ a < C i)))

def closed_in {ι : Type} (C : ι → Ordinal) (o : Ordinal) : Prop :=
  (Ordinal.IsLimit o) ∧ ∃ i : ι, C i = Ordinal.sup C

def club_in {ι : Type} (C : ι → Ordinal) (o : Ordinal) : Prop :=
  unbounded_in C o ∧ closed_in C o

def stationary_in {ι : Type} (S : ι → Ordinal) (o : Ordinal) : Prop :=
  ∀ C : ι → Ordinal, club_in C o → Ordinal_int_nonempty S C

def lt_Card (κ : Cardinal) : Set Ordinal :=
  Set.Iio κ.ord

def diag_int {ι : Type} (κ : Cardinal) (C : Ordinal → ι → Ordinal) : ι → Ordinal :=
  {β : Ordinal | β < κ.ord ∧ ∀ θ : Ordinal, θ < β → β ∈ C θ}

def Ord_fun_regressive {ι : Type} (C : ι → Ordinal) (f : Ordinal → Ordinal) : Prop :=
  ∀ c : Ordinal, ∃ i : ι, c = C i → f c < c
