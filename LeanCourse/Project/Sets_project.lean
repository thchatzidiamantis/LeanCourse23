import LeanCourse.Common
import Mathlib.Logic.Nonempty
import Mathlib.Init.Classical
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

/--Unbounded set in a limit ordinal.-/
def unbounded_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  ( Ordinal.IsLimit o ) ∧ ( (∀ a : Ordinal, (a < o → ∃ b : Ordinal, b < o ∧ b ∈ C ∧ a < b)))

/-- Our definitions require interaction between sets and ordinals. We formulate this as
restricting a set of ordinals to the subset of elements smaller than a given ordinal.-/
def Ordinal_res (C : Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {c ∈ C | c ≤ o}

lemma Ordinal_res_bdd (C : Set Ordinal) (o : Ordinal) : BddAbove (Ordinal_res C o) := by
{
  use o ; intro c hc ; exact hc.2
}

lemma res_csSup_res (C : Set Ordinal) (o : Ordinal) :
  (Ordinal_res C o) = (Ordinal_res C (sSup (Ordinal_res C o))) := by
  {
    set s := sSup (Ordinal_res C o)
    ext x ; constructor
    · intro hx
      constructor
      · exact hx.1
      · apply le_csSup
        exact Ordinal_res_bdd C o
        exact hx
    · intro hx
      constructor
      · exact hx.1
      · have : s ≤ o := by apply csSup_le' ; intro c hc ; exact hc.2
        exact le_trans hx.2 this
  }

lemma csSup_res_csSup_res (C : Set Ordinal) (o : Ordinal) :
  sSup (Ordinal_res C o) = sSup (Ordinal_res C (sSup (Ordinal_res C o))) := by
    exact congrArg sSup (res_csSup_res C o)

/--We define a set of ordinals to be a subset of any ordinal larger than the elements of the set.-/
def sub_Ordinal (C : Set Ordinal) (o : Ordinal) : Prop :=
  Ordinal_res C o = C

lemma sub_Ordinal_iff_res_eq (C : Set Ordinal) (o : Ordinal) :
  sub_Ordinal C o ↔ (∀ c ∈ C, c ≤ o) := by
    unfold sub_Ordinal ; unfold Ordinal_res
    exact Set.sep_eq_self_iff_mem_true

/--We restrict the definition of unbounded sets to subsets of the given ordinal.-/
def sub_unbounded_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  unbounded_in (Ordinal_res C o) o

--def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  --sub_unbounded_in C o ∧ (∀ b : Ordinal, b < o → ∀ g : (a : Ordinal) → a < b → Ordinal,
    --∀ i : Ordinal, (hi : i < b) → g i hi ∈ C → (Ordinal.bsup b g) ∈ C)

/--A club set is a closed unbounded set.-/
def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  sub_unbounded_in C o ∧ (∀ b : Ordinal, b < o → Set.Nonempty (Ordinal_res C b) → sSup (Ordinal_res C b) ∈ C)

/--A stationary set is a subset of an ordinal that intersects every club sets.-/
def stationary_in (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, (sub_Ordinal C o ∧ club_in C o) → Set.Nonempty (S ∩ C)

/--The diagonal intersection of a family.-/
def diag_int (κ : Cardinal) (C : Ordinal → Set Ordinal) : Set Ordinal :=
  {β : Ordinal | β < κ.ord ∧ ∀ θ : Ordinal, θ < β → β ∈ C θ}

/--A regressive function in the context opf ordinals.-/
def Ord_fun_regressive (C : Set Ordinal) (f : Ordinal → Ordinal) : Prop :=
  ∀ c : Ordinal, c ∈ C → f c < c

lemma int_two_club (C D : Set Ordinal) (κ : Cardinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : Cardinal.aleph0 < κ) (hC: club_in C κ.ord) (hD : club_in D κ.ord) :
  club_in (C ∩ D) κ.ord := by
  {
    rw [club_in, sub_unbounded_in, unbounded_in] at *
    obtain ⟨ ⟨ hC1₁, hC1₂ ⟩ , hC2 ⟩ := hC ; obtain ⟨ ⟨ hD1₁, hD1₂ ⟩ , hD2 ⟩ := hD
    constructor
    · constructor
      · exact hC1₁
      · intro a ha
        have hfg : ∃ f g : ℕ → Ordinal, ∀ n : ℕ, a < f n ∧ f n < f (n + 1) ∧ f (n) < g (n + 1) ∧
          g (n) < f (n + 1) ∧ f n ∈ C ∧ g n ∈ D := by sorry
        obtain ⟨ f, g, hfg ⟩ := hfg
        have : sSup (Set.range f) = sSup (Set.range g) := by
        {
          apply csSup_eq_csSup_of_forall_exists_le
          sorry ; sorry
        }
        set α := sSup (Set.range f)
        have hα : α < κ.ord := by sorry
        have hCα₀ : Set.Nonempty (Ordinal_res C α) := by sorry
        have hDα₀ : Set.Nonempty (Ordinal_res D α) := by sorry
        have hCα₁ : α = sSup (Ordinal_res C α) := by sorry
        have hDα₁ : α = sSup (Ordinal_res D α) := by sorry
        have hCα₂ : α ∈ C := by
          specialize hC2 α hα hCα₀ ; exact Set.mem_of_eq_of_mem hCα₁ hC2
        have hDα₂ : α ∈ D := by
          specialize hD2 α hα hDα₀ ; exact Set.mem_of_eq_of_mem hDα₁ hD2
        use α
        constructor ; exact hα
        · constructor ; constructor ; exact Set.mem_inter hCα₂ hDα₂
          · exact LT.lt.le hα
          · have hf1 : (f 1) ≤ α := by
              apply le_csSup ; exact Ordinal.bddAbove_range f ; use 1
            have hf1' : a < f 1 := by specialize hfg 1 ; exact hfg.1
            exact LT.lt.trans_le hf1' hf1
    · unfold Ordinal_res at *
      intro b hb1 hb2
      set s := sSup (Ordinal_res (C ∩ D) b)
      have hsb : s ≤ b := by apply csSup_le' ; intro c hc ; exact hc.2
      have hsκ : s < κ.ord := by exact lt_of_le_of_lt hsb hb1
      have hsCD₀ : Set.Nonempty (Ordinal_res (C ∩ D) s) := by
      {
        obtain ⟨ c, hc ⟩ := hb2 ; use c ; constructor
        · exact hc.1
        · apply le_csSup ; exact Ordinal_res_bdd (C ∩ D) b ; exact hc
      }
      have hsC₀ : Set.Nonempty (Ordinal_res C s) := by
      {
        obtain ⟨ c, hc ⟩ := hsCD₀
        use c ; constructor ; exact hc.1.1 ; exact hc.2
      }
      have hsD₀ : Set.Nonempty (Ordinal_res D s) := by
      {
        obtain ⟨ c, hc ⟩ := hsCD₀
        use c ; constructor ; exact hc.1.2 ; exact hc.2
      }
      have hsCD : s = sSup (Ordinal_res (C ∩ D) s) := by exact csSup_res_csSup_res (C ∩ D) b
      have hsC : s = sSup (Ordinal_res C s) := by
      {
        rw [←LE.le.ge_iff_eq]
        · apply csSup_le' ; intro c hc ; exact hc.2
        · have : sSup {c | c ∈ C ∩ D ∧ c ≤ s} ≤ sSup {c | c ∈ C ∧ c ≤ s} := by
          {
            apply csSup_le_csSup ; exact Ordinal_res_bdd C s
            exact hsCD₀
            intro c hc ; constructor ; exact hc.1.1 ; exact hc.2
          }
          exact Eq.trans_le hsCD this
      }
      have hsD : s = sSup (Ordinal_res D s) := by
      {
        rw [←LE.le.ge_iff_eq]
        · apply csSup_le' ; intro c hc ; exact hc.2
        · have : sSup {c | c ∈ C ∩ D ∧ c ≤ s} ≤ sSup {c | c ∈ D ∧ c ≤ s} := by
          {
            apply csSup_le_csSup ; exact Ordinal_res_bdd D s
            exact hsCD₀
            intro c hc ; constructor ; exact hc.1.2 ; exact hc.2
          }
          exact Eq.trans_le hsCD this
      }
      constructor
      · specialize hC2 s hsκ hsC₀ ; exact Set.mem_of_eq_of_mem hsC hC2
      · specialize hD2 s hsκ hsD₀ ; exact Set.mem_of_eq_of_mem hsD hD2
  }

theorem int_lt_card_club (κ l : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (hl : l < κ) (C : Set.Iio l.ord → Set Ordinal)  :
  club_in (⋂ i, C i) κ.ord := by
{
  set l' := l.ord
  have h : l' = l.ord := by rfl
  clear_value l'
  induction l' using Ordinal.limitRecOn generalizing l
  sorry
  sorry
  sorry
}

theorem diag_int_club (κ : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (C : Ordinal → Set Ordinal) (hC : ∀ o : Ordinal, club_in (C o) κ.ord) :
  club_in (diag_int κ C) κ.ord := by
{
  constructor
  · unfold sub_unbounded_in ; unfold unbounded_in
    constructor
    · refine Cardinal.ord_isLimit ?left.left.co ; exact LT.lt.le hκ₂
    · intro a ha
      sorry
  · intro b hb₁ hb₂
    set α := sSup (Ordinal_res (diag_int κ C) b)
    by_contra h'
    have hαb : α ≤ b := by
      apply csSup_le hb₂
      intro c hc ; exact hc.2
    have hακ : α < κ.ord := by
      exact lt_of_le_of_lt hαb hb₁
    have hα : sSup (Ordinal_res (diag_int κ C) α) = α := by
      exact (csSup_res_csSup_res (diag_int κ C) b).symm
    have : ∃ θ : Ordinal, θ < α ∧ α ∉ C θ := by
    {
      by_contra h'₂ ; push_neg at h'₂
      have : α ∈ (diag_int κ C) := by constructor ; exact hακ ; exact h'₂
      exact h' this
    }
    obtain ⟨ θ₀, hθ₀₁, hθ₀₂ ⟩ := this
    by_cases Set.Nonempty (Ordinal_res (C θ₀) α)
    · have hαθ₀ : sSup (Ordinal_res (C θ₀) α) ∈ C θ₀ := by
        specialize hC θ₀ ; unfold club_in at hC ; obtain ⟨ hC₁, hC₂ ⟩ := hC
        specialize hC₂ α hακ h ; exact hC₂
      have hθ₀α : sSup (Ordinal_res (C θ₀) α) < α := by
      {
        by_contra h'₂ ; push_neg at h'₂
        have : α = sSup (Ordinal_res (C θ₀) α) := by
          apply LE.le.antisymm h'₂
          apply csSup_le h ; intro d hd ; exact hd.2
        have hαθ₀' : α ∈ C θ₀ := by
          exact Set.mem_of_eq_of_mem this hαθ₀
        exact hθ₀₂ hαθ₀'
      }
      have hν : ∃ ν : Ordinal,
        ν ∈ (diag_int κ C) ∧ θ₀ < ν ∧ ν ≤ α ∧ sSup (Ordinal_res (C θ₀) α) < ν := by
        {
          sorry --apply exists_lt_of_lt_csSup
        }
      obtain ⟨ ν, hν₁, hν₂, hν₃, hν₄ ⟩ := hν
      obtain hν' := hν₁.2
      by_cases hνθ₀ : ν ∈ C θ₀
      · apply not_mem_of_csSup_lt hν₄ ?_
        · constructor ; exact hνθ₀ ; exact hν₃
        · exact Ordinal_res_bdd (C θ₀) α
      · specialize hν' θ₀ hν₂
        exact hνθ₀ hν'
    · have hν : ∃ ν : Ordinal, ν ∈ (diag_int κ C) ∧ θ₀ < ν ∧ ν ≤ α := by
        {
          sorry
        }
      obtain ⟨ ν, hν₁, hν₂, hν₃ ⟩ := hν
      obtain hν' := hν₁.2
      by_cases hνθ₀ : ν ∈ C θ₀
      · have : ν ∈ (Ordinal_res (C θ₀) α) := by
          constructor ; exact hνθ₀ ; exact hν₃
        rw [Set.nonempty_def] at h ; push_neg at h ; specialize h ν this ; exact h
      · specialize hν' θ₀ hν₂
        exact hνθ₀ hν'
}

/--Fodor's Lemma: A regressive function on a stationary set is constant
on a stationary subset of its domain.-/
theorem regressive_on_stationary (S : Set Ordinal) (κ : Cardinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : Cardinal.aleph0 < κ) (hS : stationary_in S κ.ord) (f : Ordinal → Ordinal)
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
        · refine diag_int_club κ hκ₁ hκ₂ C' ?hC'
          intro o
          specialize hC' o
          exact hC'.1.2
      }
    have hSC : Set.Nonempty (S ∩ C) := by specialize hS C hC ; exact hS
    obtain ⟨ α, hα ⟩  := hSC
    have hαS : α ∈ S := by exact Set.mem_of_mem_inter_left hα
    have hαC : α ∈ C := by exact Set.mem_of_mem_inter_right hα
    have hα : ∀ β : Ordinal, β < α → f α ≠ β := by
    {
      intro β hβ
      simp at hαC ; rw [diag_int] at hαC ; simp at hαC ; obtain ⟨ _, hαC2 ⟩ := hαC
      specialize hαC2 β hβ
      specialize hC' β
      obtain ⟨ _, hC'2 ⟩ := hC'
      rw [@Set.not_nonempty_iff_eq_empty, @Set.eq_empty_iff_forall_not_mem] at hC'2
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
