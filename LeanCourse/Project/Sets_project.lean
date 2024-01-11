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
  (o.IsLimit) ∧ ((∀ a : Ordinal, (a < o → ∃ b : Ordinal, b < o ∧ b ∈ C ∧ a < b)))

/-- Our definitions require interaction between sets and ordinals. We formulate this as
restricting a set of ordinals to the subset of elements smaller than a given ordinal.-/
def Ordinal_res (C : Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {c ∈ C | c ≤ o}

lemma Ordinal_res_bdd' (C : Set Ordinal) (o : Ordinal) : o ∈ upperBounds (Ordinal_res C o) := by
{
  intro c hc ; exact hc.2
}

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
      · have : s ≤ o := by
          apply csSup_le' ; exact Ordinal_res_bdd' C o
        exact le_trans hx.2 this
  }

lemma csSup_res_csSup_res (C : Set Ordinal) (o : Ordinal) :
  sSup (Ordinal_res C o) = sSup (Ordinal_res C (sSup (Ordinal_res C o))) := by
    exact congrArg sSup (res_csSup_res C o)

lemma csSup_lbd (C : Set Ordinal) (o : Ordinal) (hC₁ : C.Nonempty)
  (ho : o < sSup C) : sSup {c ∈ C | o < c} = sSup C := by
  {
    apply csSup_eq_csSup_of_forall_exists_le
    · intro x hx
      use x
      constructor
      · exact hx.1
      · exact Eq.le rfl
    · intro y hy
      by_cases o < y
      · use y ; constructor
        · constructor
          exact hy ; exact h
        · exact Eq.le rfl
      · push_neg at h
        obtain ⟨ z, hz ⟩ := exists_lt_of_lt_csSup hC₁ ho
        use z ; constructor
        · constructor
          exact hz.1 ; exact hz.2
        apply le_of_lt ; exact LE.le.trans_lt h hz.2
  }

lemma nonempty_lbd_of_sup (C : Set Ordinal) (o : Ordinal) (hC₁ : C.Nonempty)
  (ho : o < sSup C) : Set.Nonempty {c ∈ C | o < c} := by
  {
    by_contra h' ; rw [@Set.not_nonempty_iff_eq_empty] at h'
    obtain h₂ := csSup_lbd C o hC₁ ho
    rw [h'] at h₂
    have h₃ : sSup C = ⊥ := by rw [← h₂] ; exact csSup_empty
    obtain h := ne_bot_of_gt ho
    exact h h₃
  }

/--We define a set of ordinals to be a subset of any ordinal larger than the elements of the set.-/
def sub_Ordinal (C : Set Ordinal) (o : Ordinal) : Prop :=
  Ordinal_res C o = C

lemma sub_Ordinal_iff_res_eq (C : Set Ordinal) (o : Ordinal) :
  sub_Ordinal C o ↔ (∀ c ∈ C, c ≤ o) := by
    unfold sub_Ordinal ; unfold Ordinal_res
    exact Set.sep_eq_self_iff_mem_true

/--A club set is a closed unbounded set.-/
def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  unbounded_in C o ∧ (∀ b : Ordinal, b < o → Set.Nonempty (Ordinal_res C b) → sSup (Ordinal_res C b) ∈ C)

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
    rw [club_in, unbounded_in] at *
    obtain ⟨ ⟨ hC1₁, hC1₂ ⟩ , hC2 ⟩ := hC ; obtain ⟨ ⟨ hD1₁, hD1₂ ⟩ , hD2 ⟩ := hD
    constructor
    · constructor
      · exact hC1₁
      · intro a ha
        have hfg : ∃ f g : ℕ → Ordinal, ∀ n : ℕ, a < f n ∧ f n < f (n + 1) ∧ f (n) < g (n + 1) ∧
          g (n) < f (n + 1) ∧ f n ∈ C ∧ g n ∈ D ∧ f n < κ.ord := by
        {
          sorry
        }
        obtain ⟨ f, g, hfg ⟩ := hfg
        have : sSup (Set.range f) = sSup (Set.range g) := by
        {
          apply csSup_eq_csSup_of_forall_exists_le
          · intro x hx
            obtain ⟨ n, hn ⟩ := hx
            use g (n + 1)
            constructor
            · exact Set.mem_range_self (n + 1)
            · specialize hfg n
              obtain h := hfg.2.2.1 --f n < g (n + 1) (for later, b/c might change hfg)
              rw [← hn]
              exact LT.lt.le h
          · intro x hx
            obtain ⟨ n, hn ⟩ := hx
            use f (n + 1)
            constructor
            · exact Set.mem_range_self (n + 1)
            · specialize hfg n
              obtain h := hfg.2.2.2.1 --g n < f (n + 1)
              rw [← hn]
              exact LT.lt.le h
        }
        set α := sSup (Set.range f)
        have hα : α < κ.ord := by
        {
          have hn : ∀ n : ℕ, f n < κ.ord := by
            intro n ; specialize hfg n
            exact hfg.2.2.2.2.2.2 -- f n < κ.ord
          exact Cardinal.sup_lt_ord_lift_of_isRegular hκ₁ hκ₂ hn
        }
        have hCα₀ : Set.Nonempty (Ordinal_res C α) := by
        {
          use f 0 ; specialize hfg 0
          constructor
          · exact hfg.2.2.2.2.1 --f 0 ∈ C
          · apply le_csSup
            exact Ordinal.bddAbove_range f
            use 0
        }
        have hDα₀ : Set.Nonempty (Ordinal_res D α) := by
        {
          use g 0 ; specialize hfg 0
          constructor
          · exact hfg.2.2.2.2.2.1 --g 0 ∈ D
          · rw [this]
            apply le_csSup
            exact Ordinal.bddAbove_range g
            use 0
        }
        have hCα₁ : α = sSup (Ordinal_res C α) := by
        {
          apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
          · exact Set.range_nonempty f
          · intro d hd
            obtain ⟨ y, hy ⟩ := hd ; rw [← hy]
            specialize hfg y
            apply le_csSup
            · exact Ordinal_res_bdd C α
            · constructor
              · exact hfg.2.2.2.2.1 --f y ∈ C
              · apply le_csSup
                · exact Ordinal.bddAbove_range f
                · use y
          · intro w hw
            apply exists_lt_of_lt_csSup
            · exact Set.range_nonempty f
            · have hw₂ : sSup (Ordinal_res C α) ≤ α := by
                apply csSup_le'
                exact Ordinal_res_bdd' C α
              exact LT.lt.trans_le hw hw₂
        }
        have hDα₁ : α = sSup (Ordinal_res D α) := by
        {
          rw [this]
          apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
          · exact Set.range_nonempty g
          · intro d hd
            obtain ⟨ y, hy ⟩ := hd ; rw [← hy]
            specialize hfg y
            apply le_csSup
            · exact Ordinal_res_bdd D (sSup (Set.range g))
            · constructor
              · exact hfg.2.2.2.2.2.1 --g y ∈ D
              · apply le_csSup
                · exact Ordinal.bddAbove_range g
                · use y
          · intro w hw
            apply exists_lt_of_lt_csSup
            · exact Set.range_nonempty g
            · have hw₂ : sSup (Ordinal_res D (sSup (Set.range g))) ≤ sSup (Set.range g) := by
                apply csSup_le'
                exact Ordinal_res_bdd' D (sSup (Set.range g))
              exact LT.lt.trans_le hw hw₂
        }
        have hCα₂ : α ∈ C := by
          specialize hC2 α hα hCα₀ ; exact Set.mem_of_eq_of_mem hCα₁ hC2
        have hDα₂ : α ∈ D := by
          specialize hD2 α hα hDα₀ ; exact Set.mem_of_eq_of_mem hDα₁ hD2
        use α
        constructor ; exact hα
        · constructor
          · constructor
            · exact hCα₂
            · exact hDα₂
          · have hf1 : (f 1) ≤ α := by
              apply le_csSup ; exact Ordinal.bddAbove_range f ; use 1
            have hf1' : a < f 1 := by specialize hfg 1 ; exact hfg.1
            exact LT.lt.trans_le hf1' hf1
    · unfold Ordinal_res at *
      intro b hb1 hb2
      set s := sSup (Ordinal_res (C ∩ D) b)
      have hsb : s ≤ b := by
        apply csSup_le' ; exact Ordinal_res_bdd' (C ∩ D) b
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
        · apply csSup_le' ; exact Ordinal_res_bdd' C s
        · have : sSup {c | c ∈ C ∩ D ∧ c ≤ s} ≤ sSup {c | c ∈ C ∧ c ≤ s} := by
          {
            apply csSup_le_csSup ; exact Ordinal_res_bdd C s
            exact hsCD₀
            intro c hc ; constructor
            · exact hc.1.1
            · exact hc.2
          }
          exact Eq.trans_le hsCD this
      }
      have hsD : s = sSup (Ordinal_res D s) := by
      {
        rw [←LE.le.ge_iff_eq]
        · apply csSup_le' ; exact Ordinal_res_bdd' D s
        · have : sSup {c | c ∈ C ∩ D ∧ c ≤ s} ≤ sSup {c | c ∈ D ∧ c ≤ s} := by
          {
            apply csSup_le_csSup ; exact Ordinal_res_bdd D s
            exact hsCD₀
            intro c hc ; constructor
            · exact hc.1.2
            · exact hc.2
          }
          exact Eq.trans_le hsCD this
      }
      constructor
      · specialize hC2 s hsκ hsC₀ ; exact Set.mem_of_eq_of_mem hsC hC2
      · specialize hD2 s hsκ hsD₀ ; exact Set.mem_of_eq_of_mem hsD hD2
  }

theorem int_lt_card_club (κ μ : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (hμ : μ.ord > 0) (hμκ : μ < κ) (C : Ordinal → Set Ordinal) (hC : ∀ i : Ordinal, club_in (C i) κ.ord) :
  club_in (⋂ i : Set.Iio μ.ord, C i) κ.ord := by
{
  set l := μ.ord
  have hl : l = μ.ord := by rfl
  clear_value l
  induction l using Ordinal.limitRecOn generalizing μ
  · exfalso
    exact LT.lt.false hμ
  · by_cases μ.ord = 1
    · specialize hC 0
      have h1 : Set.Iio 1 = {0} := by sorry
      have : (⋂ i : Set.Iio 1, C i) = C 0 := by
        sorry
      --exact eq_club_club (C 0) (⋂ i, C i) κ.ord this.symm : not working because of coe problems
      sorry
    · sorry
  · sorry
}

theorem diag_int_club (κ : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (C : Ordinal → Set Ordinal) (hC : ∀ o : Ordinal, club_in (C o) κ.ord) :
  club_in (diag_int κ C) κ.ord := by
{
  constructor
  · unfold unbounded_in
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
    have hα₂ : Set.Nonempty (Ordinal_res (diag_int κ C) α) := by
      rw [← res_csSup_res] ; exact hb₂
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
      have hv : ∃ v : Ordinal,
        v ∈ (diag_int κ C) ∧ θ₀ < v ∧ v ≤ α ∧ sSup (Ordinal_res (C θ₀) α) < v := by
        {
          have h₄ : Set.Nonempty {x ∈ (Ordinal_res (diag_int κ C) α) |
            (max (sSup (Ordinal_res (C θ₀) α)) θ₀) < x} := by
          {
            refine nonempty_lbd_of_sup (Ordinal_res (diag_int κ C) α)
              (max (sSup (Ordinal_res (C θ₀) α)) θ₀) hα₂ ?_
            apply max_lt
            exact Eq.trans_gt (id hα.symm) hθ₀α
            exact Eq.trans_gt (id hα.symm) hθ₀₁
          }
          obtain ⟨ x, hx₁, hx₂ ⟩ := h₄
          obtain ⟨ hx₃, hx₄ ⟩ := max_lt_iff.1 hx₂
          use x ; constructor
          · exact hx₁.1
          · constructor
            · exact hx₄
            · constructor ; exact hx₁.2 ; exact hx₃
        }
      obtain ⟨ v, hv₁, hv₂, hv₃, hv₄ ⟩ := hv
      obtain hv' := hv₁.2
      by_cases hvθ₀ : v ∈ C θ₀
      · apply not_mem_of_csSup_lt hv₄ ?_
        · constructor ; exact hvθ₀ ; exact hv₃
        · exact Ordinal_res_bdd (C θ₀) α
      · specialize hv' θ₀ hv₂
        exact hvθ₀ hv'
    · have hv : ∃ v : Ordinal, v ∈ (diag_int κ C) ∧ θ₀ < v ∧ v ≤ α := by
        {
          sorry
        }
      obtain ⟨ v, hv₁, hv₂, hv₃ ⟩ := hv
      obtain hv' := hv₁.2
      by_cases hvθ₀ : v ∈ C θ₀
      · have : v ∈ (Ordinal_res (C θ₀) α) := by
          constructor ; exact hvθ₀ ; exact hv₃
        rw [Set.nonempty_def] at h ; push_neg at h ; specialize h v this ; exact h
      · specialize hv' θ₀ hv₂
        exact hvθ₀ hv'
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

/-
To do:

• Find a way to construct the f and g in the two set intersection proof
• Get induction to work for int_lt_card_club
• diag_int_club unboundedness proof
• Make a lemma for showing nonemptiness
• make a lemma for sups of Ordinal_res of supersets
 -/
