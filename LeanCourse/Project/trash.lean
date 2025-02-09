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

lemma strict_res_csSup_res' {C : Set Ordinal} {o : Ordinal}
  (hCo₁ : ∀ x ∈ (strict_Ordinal_res C o), x < sSup (strict_Ordinal_res C o))
  (hCo₂ : (strict_Ordinal_res C o).Nonempty) :
    strict_Ordinal_res C o = strict_Ordinal_res C (sSup (strict_Ordinal_res C o)) := by
  {
    sorry
  }

theorem int_two_club (C D : Set Ordinal) (κ : Cardinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : Cardinal.aleph0 < κ) (hC: club_in C κ.ord) (hD : club_in D κ.ord) :
  club_in (C ∩ D) κ.ord := by
  {
    obtain hCD := int_two_club_unbounded C D κ hκ₁ hκ₂ hC hD
    constructor
    · exact hCD
    · obtain ⟨ _ , hC2 ⟩ := hC ; obtain ⟨ _, hD2 ⟩ := hD
      --unfold strict_Ordinal_res at *
      intro b hb1 hb2
      set s := sSup (strict_Ordinal_res (C ∩ D) b)
      have hsb : s ≤ b := by
        apply csSup_le' ; exact strict_Ordinal_res_bdd' (C ∩ D) b
      have hsκ : s < κ.ord := by exact lt_of_le_of_lt hsb hb1
      have hsCD₀ : Set.Nonempty (strict_Ordinal_res (C ∩ D) s) := by
      {
        obtain ⟨ c, hc ⟩ := hb2 ; use c ; constructor
        · exact hc.1
        · apply lt_csSup_of_lt
          · exact strict_Ordinal_res_bdd (C ∩ D) b
          · sorry
          · sorry
          · sorry
      }
      have hsC₀ : Set.Nonempty (strict_Ordinal_res C s) := by
      {
        obtain ⟨ c, hc ⟩ := hsCD₀
        use c ; constructor ; exact hc.1.1 ; exact hc.2
      }
      have hsD₀ : Set.Nonempty (strict_Ordinal_res D s) := by
      {
        obtain ⟨ c, hc ⟩ := hsCD₀
        use c ; constructor ; exact hc.1.2 ; exact hc.2
      }
      have hsC : s = sSup (strict_Ordinal_res C s) := by
      {
        rw [←LE.le.ge_iff_eq]
        · apply csSup_le' ; exact strict_Ordinal_res_bdd' C s
        · sorry
      }
      have hsD : s = sSup (strict_Ordinal_res D s) := by
      {
        rw [←LE.le.ge_iff_eq]
        · apply csSup_le' ; exact strict_Ordinal_res_bdd' D s
        · sorry
      }
      constructor
      · specialize hC2 s hsκ hsC₀ ; exact Set.mem_of_eq_of_mem hsC hC2
      · specialize hD2 s hsκ hsD₀ ; exact Set.mem_of_eq_of_mem hsD hD2
  }


/-This needs a definition of strict ordinal res : we need to have at least one element smaller than o

lemma unbounded_iff (C : Set Ordinal) (o : Ordinal) (ho₁ : o.IsLimit) (ho₂ : Set.Nonempty (Ordinal_res C o)) :
  unbounded_in C o ↔ sSup (Ordinal_res C o) = o := by
  {
    constructor
    · exact fun a ↦ csSup_of_unbounded a ho₂
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


/-

Stuff I did with Ordinal_res

noncomputable def unbounded_choice {C : Set Ordinal} {o : Ordinal} (a : Ordinal)
  (hC: unbounded_in C o) : Ordinal :=
    if ha : a < o then Exists.choose (hC.2 a ha)
    else 0
--Exists.choose spec

noncomputable def nested_unbounded_choice {C D : Set Ordinal} (o a: Ordinal)
  (hC: unbounded_in C o) (hD : unbounded_in D o) (ha : a < o) : ℕ → Ordinal × Ordinal
  | 0 => (unbounded_choice a hC, unbounded_choice a hD)
  | n + 1 => (unbounded_choice (nested_unbounded_choice o a hC hD ha n).2 hC,
    unbounded_choice (nested_unbounded_choice o a hC hD ha n).1 hD)

lemma unbounded_choice_lt {C : Set Ordinal} {o : Ordinal} (a : Ordinal)
  (hC: unbounded_in C o) (ha : a < o) : unbounded_choice a hC < o := by
    unfold unbounded_choice
    simp [ha]
    exact (Exists.choose_spec (hC.2 a ha)).1

lemma int_two_club (C D : Set Ordinal) (κ : Cardinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : Cardinal.aleph0 < κ) (hC: club_in C κ.ord) (hD : club_in D κ.ord) :
  club_in (C ∩ D) κ.ord := by
  {
    rw [club_in, unbounded_in] at *
    constructor
    · constructor
      · exact hC.1.1
      · intro a ha
        have hfg : ∃ f g : ℕ → Ordinal, ∀ n : ℕ, a < f 0 ∧  f (n) < g (n + 1) ∧
          g (n) < f (n + 1) ∧ f n ∈ C ∧ g n ∈ D ∧ f n < κ.ord := by
        {
          set f := fun n ↦ (nested_unbounded_choice κ.ord a hC.1 hD.1 ha n).1 ; use f
          set g := fun n ↦ (nested_unbounded_choice κ.ord a hC.1 hD.1 ha n).2 ; use g
          intro n
          refine ⟨ ?_, ?_, ?_, ?_, ?_, ?_⟩
          · sorry
          · sorry
          · sorry
          · sorry
          · sorry
          · sorry
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
              obtain h := hfg.2.1 --f n < g (n + 1) (for later, b/c might change hfg)
              rw [← hn]
              exact LT.lt.le h
          · intro x hx
            obtain ⟨ n, hn ⟩ := hx
            use f (n + 1)
            constructor
            · exact Set.mem_range_self (n + 1)
            · specialize hfg n
              obtain h := hfg.2.2.1 --g n < f (n + 1)
              rw [← hn]
              exact LT.lt.le h
        }
        set α := sSup (Set.range f)
        have hα : α < κ.ord := by
        {
          have hn : ∀ n : ℕ, f n < κ.ord := by
            intro n ; specialize hfg n
            exact hfg.2.2.2.2.2 -- f n < κ.ord
          exact Cardinal.sup_lt_ord_lift_of_isRegular hκ₁ hκ₂ hn
        }
        have hCα₀ : Set.Nonempty (Ordinal_res C α) := by
        {
          use f 0 ; specialize hfg 0
          constructor
          · exact hfg.2.2.2.1 --f 0 ∈ C
          · apply le_csSup
            exact Ordinal.bddAbove_range f
            use 0
        }
        have hDα₀ : Set.Nonempty (Ordinal_res D α) := by
        {
          use g 0 ; specialize hfg 0
          constructor
          · exact hfg.2.2.2.2.1 --g 0 ∈ D
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
              · exact hfg.2.2.2.1 --f y ∈ C
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
              · exact hfg.2.2.2.2.1 --g y ∈ D
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
          obtain ⟨ _ , hC2 ⟩ := hC
          specialize hC2 α hα hCα₀ ; exact Set.mem_of_eq_of_mem hCα₁ hC2
        have hDα₂ : α ∈ D := by
          obtain ⟨ _ , hD2 ⟩ := hD
          specialize hD2 α hα hDα₀ ; exact Set.mem_of_eq_of_mem hDα₁ hD2
        use α
        refine ⟨ hα, ⟨ hCα₂, hDα₂ ⟩, ?_  ⟩
        have hf0 : (f 0) ≤ α := by
          apply le_csSup ; exact Ordinal.bddAbove_range f ; use 0
        have hf0' : a < f 0 := by specialize hfg 0 ; exact hfg.1
        exact LT.lt.trans_le hf0' hf0
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
      obtain ⟨ _ , hC2 ⟩ := hC ; obtain ⟨ _, hD2 ⟩ := hD
      constructor
      · specialize hC2 s hsκ hsC₀ ; exact Set.mem_of_eq_of_mem hsC hC2
      · specialize hD2 s hsκ hsD₀ ; exact Set.mem_of_eq_of_mem hsD hD2
  }

-/theorem int_lt_card_club (κ μ : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
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
      have h1 : Set.Iio (1 : Ordinal) = {0} := by sorry
      have : (⋂ i : Set.Iio (1 : Ordinal), C i) = C 0 := by
        sorry
      sorry
    · sorry
  · sorry
}

/-Starting with cardinals, with l > 0 and Iio:
  · exfalso
    exact LT.lt.false hl
  · by_cases a✝ = 1
    · specialize hC 0
      have h1 : Set.Iio (1 : Ordinal) = {0} := by sorry
      have : (⋂ i : Set.Iio (1 : Ordinal), C i) = C 0 := by
        sorry
      sorry
    · sorry
  · sorry-/

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
          have h₄ : Set.Nonempty {x ∈ (Ordinal_res (diag_int κ C) α) | θ₀ < x} := by
            refine nonempty_lbd_of_sup (Ordinal_res (diag_int κ C) α) θ₀ hα₂ ?_
            exact Eq.trans_gt (id hα.symm) hθ₀₁
          obtain ⟨ x, hx₁, hx₂ ⟩ := h₄
          use x ; constructor
          · exact hx₁.1
          · constructor
            · exact hx₂
            · exact hx₁.2
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
-/


theorem int_lt_card_sub_club {κ : Cardinal} (l : Ordinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : Cardinal.aleph0 < κ) (hlκ : l.card < κ) (C : Ordinal → Set Ordinal)
  (hC : ∀ i : Ordinal, i < l → club_in (C i) κ.ord)
  (hCsub : ∀ a d : Ordinal, a < d → C d ⊆ C a) (nontriv : 0 < l):
    club_in (⋂ i : Set.Iio l, (C i)) κ.ord := by
  {
    induction l, nontriv using Ordinal.limitRecOn
    case H₁ =>
      exfalso
      exact LT.lt.false nontriv
    case H₂ d hd =>
      have : (⋂ i : Set.Iio (Order.succ d), (C i)) = --Make this a lemma
        (⋂ i : Set.Iio d, (C i)) ∩ (C d) :=by
        {
          ext x ; constructor
          · intro hx ; simp [Set.iInter_coe_set] at *
            constructor
            · intro i hi
              refine hx i ?_
              exact LT.lt.le hi
            · refine hx d (le_of_eq ?_) ; rfl
          · intro hx ; simp [Set.iInter_coe_set] at * ; obtain ⟨ hx₁, hx₂ ⟩ := hx
            intro i hi
            rw [@le_iff_lt_or_eq] at hi
            obtain hi₁|hi₂ := hi
            exact hx₁ i hi₁
            rw [hi₂] ; exact hx₂
        }
      rw [this]
      apply int_two_club
      · rw [Cardinal.IsRegular.cof_eq hκ₁] ; exact hκ₂
      · apply hd
        · rw [← @Cardinal.lt_ord] at *
          obtain hyp := Order.lt_succ d
          exact gt_trans hlκ hyp
        · intro i hi
          have hisd : i < Order.succ d := by rw [@Order.lt_succ_iff] ; exact LT.lt.le hi
          exact hC i hisd
        · sorry
      · exact hC d (Order.lt_succ d)
    sorry
  }
