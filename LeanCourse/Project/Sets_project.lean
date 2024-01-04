import LeanCourse.Common
import Mathlib.Logic.Nonempty
import Mathlib.Init.Classical
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic


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

-- def closed_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  -- (Ordinal.IsLimit o) ∧ (∀ a : Ordinal, sorry) --how to sup???

-- def sub_closed_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  -- closed_in (Ordinal_res C o) o

--def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  --sub_unbounded_in C o ∧ (∀ b : Ordinal, b < o → ∀ g : (a : Ordinal) → a < b → Ordinal,
    --∀ i : Ordinal, (hi : i < b) → g i hi ∈ C → (Ordinal.bsup b g) ∈ C)

def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  sub_unbounded_in C o ∧ (∀ b : Ordinal, b < o → Ordinal_res C b ≠ ∅ → sSup (Ordinal_res C b) ∈ C)

def stationary_in (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, (sub_Ordinal C o ∧ club_in C o) → S ∩ C ≠ ∅

def lt_Card (κ : Cardinal) : Set Ordinal :=
  Set.Iio κ.ord

def diag_int (κ : Cardinal) (C : Ordinal → Set Ordinal) : Set Ordinal :=
  {β : Ordinal | β < κ.ord ∧ ∀ θ : Ordinal, θ < β → β ∈ C θ}

def Ord_fun_regressive (C : Set Ordinal) (f : Ordinal → Ordinal) : Prop :=
  ∀ c : Ordinal, c ∈ C → f c < c

lemma int_two_club (C D : Set Ordinal) (o : Ordinal) (hC: club_in C o) (hD : club_in D o) :
  club_in (C ∩ D) o := by
  {
    rw [club_in, sub_unbounded_in, unbounded_in] at *
    obtain ⟨ hC1, hC2 ⟩ := hC ; obtain ⟨ hD1, hD2 ⟩ := hD
    constructor
    · constructor
      · exact hC1.1
      · intro a ha
        sorry
    · unfold Ordinal_res at *
      intro b hb1 hb2
      set s := sSup {c | c ∈ C ∩ D ∧ c ≤ b}
      have hsC : s = sSup {c | c ∈ C ∧ c ≤ s} := by sorry
      have hsD : s = sSup {c | c ∈ D ∧ c ≤ s} := by sorry
      have hsb : s < b := by sorry
      have hso : s < o := by exact gt_trans hb1 hsb
      have hsC' : {c | c ∈ C ∧ c ≤ s} ≠ ∅ := by sorry
      --{
        --have : {c | c ∈ C ∧ c ≤ s} ⊆ {c | c ∈ C ∧ c ≤ b} := by
        ----{
          --intro x hx ; simp ; constructor
          --· exact Set.mem_of_mem_inter_left hx
          --· have : x ≤ s := by simp ; simp at hx ; exact hx.2
            --apply le_of_lt ; exact lt_of_le_of_lt this hsb
        --}
        --by_contra h'
        --have h'' :
      --}
      have hsD' : {c | c ∈ D ∧ c ≤ s} ≠ ∅ := by sorry
      constructor
      · specialize hC2 s hso hsC' ; exact Set.mem_of_eq_of_mem hsC hC2
      · specialize hD2 s hso hsD' ; exact Set.mem_of_eq_of_mem hsD hD2
  }

theorem int_lt_card_club (κ l : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : ℵ₀ < κ)
  (hl : l < κ) (C : lt_Card l → Set Ordinal)  :
  club_in (⋂ i, C i) κ.ord := by
{
  sorry
}

theorem diag_int_club (κ : Cardinal) (hκ : ℵ₀ < κ) (C : Ordinal → Set Ordinal)
  (hC : ∀ o : Ordinal, club_in (C o) κ.ord) :
  club_in (diag_int κ C) κ.ord := by
{
  constructor
  · unfold sub_unbounded_in ; unfold unbounded_in
    constructor
    · refine Cardinal.ord_isLimit ?left.left.co ; exact LT.lt.le hκ
    · intro a ha
      sorry
  · intro b hb1 hb2
    set α := sSup (Ordinal_res (diag_int κ C) b)
    by_contra h'
    have hακ : α < κ.ord := by sorry
    have hα : sSup (Ordinal_res (diag_int κ C) α) = α := by
    {
      apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
      · sorry
      · intro a ha ; unfold Ordinal_res at ha ; exact ha.2
      · intro w hw ; sorry
    }
    unfold diag_int at *
    have : ∃ θ : Ordinal, θ < α ∧ α ∉ C θ := by
    {
      sorry
    }
    obtain ⟨ θ, hθ₁, hθ₂  ⟩ := this
    by_cases Ordinal_res (C θ) α ≠ ∅
    · have hαθ : sSup (Ordinal_res (C θ) α) ∈ C θ := by
      {
        specialize hC θ ; unfold club_in at hC ; obtain ⟨ hC₁, hC₂ ⟩ := hC
        specialize hC₂ α hακ h ; exact hC₂
      }
      sorry
    push_neg at h
    sorry
}

/--Fodor's Lemma: A regressive function on a stationary set is constant on a stationary subset of its domain-/
theorem regressive_on_stationary (S : Set Ordinal) (κ : Cardinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : ℵ₀ < κ) (hS : stationary_in S κ.ord) (f : Ordinal → Ordinal)
  (hf : Ord_fun_regressive S f) :
    ∃ θ: Ordinal, stationary_in (f⁻¹' ({θ})) κ.ord := by
  {
    by_contra h' ; push_neg at h'
    unfold stationary_in at * ; push_neg at h'
    choose C' hC' using h'
    let C := diag_int κ C'
    have hC : ( sub_Ordinal C κ.ord ) ∧ ( club_in C κ.ord ) := by
      {
        constructor
        · apply (sub_Ordinal_iff_res_eq C (Cardinal.ord κ)).2
          intro c hc
          simp at hc ; rw [diag_int] at hc ; simp at hc ;  exact LT.lt.le hc.1
        · refine diag_int_club κ hκ₂ C' ?hC'
          intro o
          specialize hC' o
          exact hC'.1.2
      }
    have hSC : S ∩ C ≠ ∅ := by specialize hS C hC ; exact hS
    have hSC' : ∃ s, s∈ S ∩ C := by rw [← @Set.nonempty_iff_ne_empty] at hSC ; exact hSC
    obtain ⟨ α, hα ⟩  := hSC'
    have hαS : α ∈ S := by exact Set.mem_of_mem_inter_left hα
    have hαC : α ∈ C := by exact Set.mem_of_mem_inter_right hα
    have hα : ∀ β : Ordinal, β < α → f α ≠ β := by
    {
      intro β hβ
      simp at hαC ; rw [diag_int] at hαC ; simp at hαC ; obtain ⟨ hαC1, hαC2 ⟩ := hαC
      specialize hαC2 β hβ
      specialize hC' β
      obtain ⟨ hC'1, hC'2 ⟩ := hC'
      rw [@Set.eq_empty_iff_forall_not_mem] at hC'2
      by_contra h'
      have : α ∈ f ⁻¹' {β} ∩ C' β := by
      {
        constructor
        · exact h'
        · exact hαC2
      }
      exact hC'2 α this
    }
    unfold Ord_fun_regressive at hf
    specialize hf α hαS
    exact hα (f α) hf rfl
  }



#lint
