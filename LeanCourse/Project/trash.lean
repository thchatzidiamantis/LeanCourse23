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
  {β : Ordinal | β < κ.ord ∧ ∀ θ : Ordinal, θ < β → β ∈ (C θ)}

def Ord_fun_regressive {ι : Type} (C : ι → Ordinal) (f : Ordinal → Ordinal) : Prop :=
  ∀ c : Ordinal, ∃ i : ι, c = C i → f c < c



/-This either needs an extra assumption or has to be done within the context of club sets

lemma unbounded_iff (C : Set Ordinal) (o : Ordinal) (ho₁ : o.IsLimit) (ho₂ : Set.Nonempty (Ordinal_res C o)) :
  unbounded_in C o ↔ sSup (Ordinal_res C o) = o := by
  {
    constructor
    · unfold unbounded_in
      intro ⟨ h₁, h₂ ⟩
      apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
      · exact ho₂
      · intro a ha
        exact ha.2
      · intro w hw
        specialize h₂ w hw
        obtain ⟨ b, hb ⟩ := h₂
        use b
        constructor
        · constructor
          · exact hb.2.1
          · exact le_of_lt hb.1
        · exact hb.2.2
    · intro h
      unfold unbounded_in
      constructor
      · exact ho₁
      · intro a ha
        sorry
    sorry
  }-/


--def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  --sub_unbounded_in C o ∧ (∀ b : Ordinal, b < o → ∀ g : (a : Ordinal) → a < b → Ordinal,
    --∀ i : Ordinal, (hi : i < b) → g i hi ∈ C → (Ordinal.bsup b g) ∈ C)

/-have h₂ : sSup {x ∈ (Ordinal_res (diag_int κ C) α) |
            (max (sSup (Ordinal_res (C θ₀) α)) θ₀) < x} = sSup (Ordinal_res (diag_int κ C) α) := by
            {
              apply csSup_lbd (Ordinal_res (diag_int κ C) α) (max (sSup (Ordinal_res (C θ₀) α)) θ₀) hα₂
              apply max_lt
              · exact Eq.trans_gt (id hα.symm) hθ₀α
              · exact Eq.trans_gt (id hα.symm) hθ₀₁
            }
          have h₃ : sSup {x ∈ (Ordinal_res (diag_int κ C) α) |
            (max (sSup (Ordinal_res (C θ₀) α)) θ₀) < x} = α := by
              rw [h₂] ; exact hα
          clear h₂
          have h₄ : Set.Nonempty {x ∈ (Ordinal_res (diag_int κ C) α) |
            (max (sSup (Ordinal_res (C θ₀) α)) θ₀) < x} := by
            {
              by_contra h₄' ; rw [@Set.not_nonempty_iff_eq_empty] at h₄'
              obtain h₅ : sSup {x | x ∈ Ordinal_res (diag_int κ C) α ∧
                max (sSup (Ordinal_res (C θ₀) α)) θ₀ < x} = ⊥:= by rw [h₄'] ; exact csSup_empty
              rw [h₅] at h₃
              obtain h₆ := ne_bot_of_gt hθ₀₁
              exact h₆ (id h₃.symm)
            }-/

/-lemma eq_club_club (C D : Set Ordinal) (o : Ordinal) (h : C = D) (hC : club_in C o) : club_in D o := by
  sorry-/
