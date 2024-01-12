import LeanCourse.Common
import Mathlib.Logic.Nonempty
import Mathlib.Init.Classical
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

/-- Subset of elements smaller than a given ordinal.-/
def Ordinal_res (C : Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {c ∈ C | c ≤ o}

/--This represents the intersection of a set and an ordinal.-/
def strict_Ordinal_res (C : Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {c ∈ C | c < o}

lemma strict_res_sub_res (C : Set Ordinal) (o : Ordinal) : (strict_Ordinal_res C o) ⊆ (Ordinal_res C o) := by
  intro a ha ; exact ⟨ ha.1, le_of_lt ha.2 ⟩

theorem res_eq_strict_res_succ (C : Set Ordinal) (o : Ordinal) :
  Ordinal_res C o = strict_Ordinal_res C (Order.succ o) := by
  {
    ext x ; constructor
    · intro ⟨ hx₁, hx₂ ⟩
      refine ⟨ hx₁, ?_ ⟩
      exact Order.lt_succ_iff.mpr hx₂
    · intro ⟨ hx₁, hx₂ ⟩
      refine ⟨ hx₁, ?_ ⟩
      exact Order.lt_succ_iff.mp hx₂
  }

lemma res_nin_lt (C : Set Ordinal) (o : Ordinal) :
  o ∉ Ordinal_res C o → ∀ c : Ordinal, c ∈ Ordinal_res C o → c < o := by
  {
    contrapose!
    simp
    intro x hx₁ hx₂
    obtain h' := hx₁.2
    have : x = o := by exact le_antisymm h' hx₂
    exact Set.mem_of_eq_of_mem (id this.symm) hx₁
  }

theorem res_eq_strict_res_iff {C : Set Ordinal} {o : Ordinal} :
  (o ∉ C) ↔ (Ordinal_res C o) = (strict_Ordinal_res C o) := by
  {
    constructor
    · intro h
      have ho : o ∉ Ordinal_res C o := by
        by_contra h'
        exact h h'.1
      rw [@Set.Subset.antisymm_iff]
      constructor
      · intro x hx
        exact ⟨ hx.1, res_nin_lt C o ho x hx ⟩
      · exact strict_res_sub_res C o
    · contrapose!
      intro h
      have ho : o ∈ Ordinal_res C o := by
        refine ⟨ h, ?_ ⟩
        exact Eq.le rfl
      have : o ∉ strict_Ordinal_res C o := by
        by_contra h'
        obtain h'₂ := h'.2
        exact LT.lt.false h'₂
      exact ne_of_mem_of_not_mem' ho this
  }


lemma strict_Ordinal_res_lt {C : Set Ordinal} {o : Ordinal} : ∀ a ∈ (strict_Ordinal_res C o), a < o := by
  intro a ha ; exact ha.2

lemma Ordinal_res_le {C : Set Ordinal} {o : Ordinal} : ∀ a ∈ (Ordinal_res C o), a ≤ o := by
  intro a ha ; exact ha.2

lemma strict_Ordinal_res_bdd' (C : Set Ordinal) (o : Ordinal) : o ∈ upperBounds (strict_Ordinal_res C o) := by
  intro a ha ; exact le_of_lt ha.2

lemma Ordinal_res_bdd' (C : Set Ordinal) (o : Ordinal) : o ∈ upperBounds (Ordinal_res C o) := by
  intro a ha ; exact ha.2

lemma strict_Ordinal_res_bdd (C : Set Ordinal) (o : Ordinal) : BddAbove (strict_Ordinal_res C o) := by
  use o ; intro c hc ; exact le_of_lt hc.2

lemma Ordinal_res_bdd (C : Set Ordinal) (o : Ordinal) : BddAbove (Ordinal_res C o) := by
  use o ; intro c hc ; exact hc.2

lemma res_csSup_res /-Do it for strict res too-/ (C : Set Ordinal) (o : Ordinal) :
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

/-I think I can do this quicker with res_eq_strict_res_iff-/
lemma strict_res_csSup_res {C : Set Ordinal} {o : Ordinal}
  (hCo₁ : sSup (strict_Ordinal_res C o) ∉ (strict_Ordinal_res C o))
  (hCo₂ : (strict_Ordinal_res C o).Nonempty) :
    strict_Ordinal_res C o = strict_Ordinal_res C (sSup (strict_Ordinal_res C o)) := by
  {
    ext x ; constructor
    · intro hx
      refine ⟨ hx.1, ?_ ⟩
      by_contra h' ; push_neg at h'
      have hox : sSup (strict_Ordinal_res C o) = x := by
      {
        refine le_antisymm h' ?_
        apply le_csSup
        exact strict_Ordinal_res_bdd C o
        exact hx
      }
      rw [hox] at hCo₁
      exact hCo₁ hx
    · intro ⟨ hx₁, hx₂ ⟩
      refine ⟨ hx₁, ?_ ⟩
      have : sSup (strict_Ordinal_res C o) ≤ o := by
      {
        apply csSup_le
        · exact hCo₂
        · intro b hb
          apply le_of_lt hb.2
      }
      exact LT.lt.trans_le hx₂ this
  }

lemma strict_csSup_res_csSup_res {C : Set Ordinal} {o : Ordinal}
  (hCo₁ : sSup (strict_Ordinal_res C o) ∉ (strict_Ordinal_res C o))
  (hCo₂ : (strict_Ordinal_res C o).Nonempty) :
    sSup (strict_Ordinal_res C o) = sSup (strict_Ordinal_res C (sSup (strict_Ordinal_res C o))) := by
  exact congrArg sSup (strict_res_csSup_res hCo₁ hCo₂)

lemma strict_csSup_res_csSup_res' {C : Set Ordinal} {o : Ordinal}
  (hCo₁ : ∀ x ∈ (strict_Ordinal_res C o), x < sSup (strict_Ordinal_res C o))
  (hCo₂ : (strict_Ordinal_res C o).Nonempty) :
    sSup (strict_Ordinal_res C o) = sSup (strict_Ordinal_res C (sSup (strict_Ordinal_res C o))) := by
  {
    refine strict_csSup_res_csSup_res ?hCo₁ hCo₂
    by_contra h'
    specialize hCo₁ ( sSup (strict_Ordinal_res C o)) h'
    exact LT.lt.false hCo₁
  }


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

lemma nonempty_strict_res_of_sup {C : Set Ordinal} {o a: Ordinal} (ha : a < o)
  (hCo : sSup (strict_Ordinal_res C o) = o) : (strict_Ordinal_res C o).Nonempty := by
  {
    by_contra h' ; rw [@Set.not_nonempty_iff_eq_empty] at h'
    have : sSup (strict_Ordinal_res C o) = ⊥ := by rw [h'] ; exact csSup_empty
    obtain h := ne_bot_of_gt ha
    have h'₂ : ⊥ = o := by rw [this] at hCo ; exact hCo
    exact h (id h'₂.symm)
  }

/--This represents a set being a subset of an ordinal-/
def sub_Ordinal (C : Set Ordinal) (o : Ordinal) : Prop :=
  strict_Ordinal_res C o = C

lemma sub_Ordinal_iff_strict_res_eq (C : Set Ordinal) (o : Ordinal) :
  sub_Ordinal C o ↔ (∀ c ∈ C, c < o) := by
    unfold sub_Ordinal ; unfold strict_Ordinal_res
    exact Set.sep_eq_self_iff_mem_true

/--Like sub_Ordinal with a ≤ relation-/
def le_Ordinal (C : Set Ordinal) (o : Ordinal) : Prop :=
  Ordinal_res C o = C

lemma le_Ordinal_iff_res_eq (C : Set Ordinal) (o : Ordinal) :
  le_Ordinal C o ↔ (∀ c ∈ C, c ≤ o) := by
    unfold le_Ordinal ; unfold Ordinal_res
    exact Set.sep_eq_self_iff_mem_true

/--Unbounded set in a limit ordinal.-/
def unbounded_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  (o.IsLimit) ∧ ((∀ a : Ordinal, (a < o → ∃ b : Ordinal, b < o ∧ b ∈ C ∧ a < b)))

lemma unbounded_in_def {C : Set Ordinal} {o : Ordinal} :
  unbounded_in C o → ∀ a : Ordinal, a < o → ∃ b : Ordinal, b < o ∧ b ∈ C ∧ a < b := by
    intro hC
    exact hC.2

lemma unbounded_in_strict_res {C : Set Ordinal} {o : Ordinal} :
  unbounded_in C o → ∀ a : Ordinal, a < o → ∃ b : Ordinal, b ∈ (strict_Ordinal_res C o) ∧ a < b := by
  {
    · intro hC a ha
      obtain ⟨ b, hb ⟩ := unbounded_in_def hC a ha ; use b
      exact ⟨ ⟨ hb.2.1, hb.1 ⟩, hb.2.2 ⟩
  }

lemma unbounded_in_strict_res_iff {C : Set Ordinal} {o : Ordinal} (ho : o.IsLimit) :
  unbounded_in C o ↔ ∀ a : Ordinal, a < o → ∃ b : Ordinal, b ∈ (strict_Ordinal_res C o) ∧ a < b := by
  {
    constructor
    · exact fun a a_1 a_2 ↦ unbounded_in_strict_res a a_1 a_2
    · intro h
      refine ⟨ ho, ?_ ⟩
      intro a ha
      specialize h a ha ; obtain ⟨ b, hb ⟩ := h
      use b
      exact ⟨ hb.1.2, ⟨ hb.1.1, hb.2 ⟩ ⟩
  }

lemma unbounded_in_res {C : Set Ordinal} {o : Ordinal} :
  unbounded_in C o → ∀ a : Ordinal, a < o → ∃ b : Ordinal, b ∈ (Ordinal_res C o) ∧ a < b := by
  {
    intro hC a ha
    obtain ⟨ b, hb ⟩ := unbounded_in_def hC a ha ; use b
    exact ⟨ ⟨ hb.2.1, le_of_lt hb.1 ⟩, hb.2.2 ⟩
  }

lemma strict_res_of_unbounded_nonempty {C : Set Ordinal} {o : Ordinal} (hC : unbounded_in C o) :
  Set.Nonempty (strict_Ordinal_res C o) := by
  {
    obtain h := unbounded_in_def hC ; specialize h 0
    have : 0 < o := by
      obtain ho := hC.1
      exact Ordinal.IsLimit.pos ho
    obtain ⟨ b, hb ⟩ := h this
    use b ; exact ⟨ hb.2.1, hb.1 ⟩
  }

lemma res_of_unbounded_nonempty {C : Set Ordinal} {o : Ordinal} (hC : unbounded_in C o) :
  Set.Nonempty (Ordinal_res C o) := by
    obtain ⟨ x, hx ⟩ := strict_res_of_unbounded_nonempty hC
    use x ; exact strict_res_sub_res C o hx

lemma csSup_of_unbounded' {C : Set Ordinal} {o : Ordinal} (hC : unbounded_in C o)
  (ho : Set.Nonempty (strict_Ordinal_res C o)) : sSup (strict_Ordinal_res C o) = o := by
  {
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ho
    · intro a ha ; apply le_of_lt
      exact strict_Ordinal_res_lt a ha
    · exact fun w a ↦ unbounded_in_strict_res hC w a
  }

lemma csSup_of_unbounded {C : Set Ordinal} {o : Ordinal} (hC : unbounded_in C o) :
  sSup (Ordinal_res C o) = o := by
  {
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact res_of_unbounded_nonempty hC
    · exact Ordinal_res_le
    · exact fun w a ↦ unbounded_in_res hC w a
  }

theorem unbounded_in_iff (C : Set Ordinal) (o : Ordinal) (ho : o.IsLimit) :
     unbounded_in C o ↔ sSup (strict_Ordinal_res C o) = o := by
    {
      constructor
      · intro h
        obtain ho₂ := strict_res_of_unbounded_nonempty h
        exact csSup_of_unbounded' h ho₂
      · intro h
        rw [unbounded_in_strict_res_iff ho]
        · intro a ha
          have ho₂ : o ≤ sSup (strict_Ordinal_res C o) := by exact Eq.le (id h.symm)
          rw [le_csSup_iff] at ho₂
          by_contra h' ; push_neg at h'
          have : a ∈ upperBounds (strict_Ordinal_res C o) := by
          {
            rw [@mem_upperBounds] ; intro x hx
            specialize h' x hx ; exact h'
          }
          specialize ho₂ a this
          obtain h'' := lt_of_le_of_lt ho₂ ha
          exact LT.lt.false h''
          · exact strict_Ordinal_res_bdd C o
          · exact nonempty_strict_res_of_sup ha h
    }

/--A club set is a closed unbounded set.-/
def club_in (C : Set Ordinal) (o : Ordinal) : Prop :=
  unbounded_in C o ∧ (∀ b : Ordinal, b < o → Set.Nonempty (strict_Ordinal_res C b) →
  sSup (strict_Ordinal_res C b) ∈ C)

def club_in' (C : Set Ordinal) (o : Ordinal) : Prop :=
  unbounded_in C o ∧ (∀ b : Ordinal, b < o → Set.Nonempty (Ordinal_res C b) → sSup (Ordinal_res C b) ∈ C)

/-I am pretty sure I can also prove the converse
theorem club'_of_club {C : Set Ordinal} {o : Ordinal} : club_in C o → club_in' C o := by
{
  · intro hC
    sorry
} -/

/--A stationary set is a subset of an ordinal that intersects every club sets.-/
def stationary_in (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, (sub_Ordinal C o ∧ club_in C o) → Set.Nonempty (S ∩ C)

/--The diagonal intersection of a family.-/
def diag_int (κ : Cardinal) (C : Ordinal → Set Ordinal) : Set Ordinal :=
  {β : Ordinal | β < κ.ord ∧ ∀ θ : Ordinal, θ < β → β ∈ C θ}

/--A regressive function in the context opf ordinals.-/
def Ord_fun_regressive (C : Set Ordinal) (f : Ordinal → Ordinal) : Prop :=
  ∀ c : Ordinal, c ∈ C → f c < c

noncomputable def unbounded_choice {C : Set Ordinal} {o : Ordinal} (a : Ordinal)
  (hC: unbounded_in C o) : Ordinal :=
    if ha : a < o then Exists.choose (hC.2 a ha)
    else 0

noncomputable def nested_unbounded_choice {C D : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (hD : unbounded_in D o) (ha : a < o) : ℕ → Ordinal × Ordinal
  | 0 => (unbounded_choice a hC, unbounded_choice a hD)
  | n + 1 => (unbounded_choice (nested_unbounded_choice hC hD ha n).2 hC,
    unbounded_choice (nested_unbounded_choice hC hD ha n).1 hD)

lemma unbounded_choice_lt {C : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (ha : a < o) : unbounded_choice a hC < o := by
    unfold unbounded_choice
    simp [ha]
    exact (Exists.choose_spec (hC.2 a ha)).1

lemma nested_unbounded_choice_lt {C D : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (hD : unbounded_in D o) (ha : a < o) (n : ℕ) :
  (nested_unbounded_choice hC hD ha n).1 < o ∧ (nested_unbounded_choice hC hD ha n).2 < o:= by
  {
    induction n
    case zero =>
      exact ⟨ unbounded_choice_lt hC ha, unbounded_choice_lt hD ha ⟩
    case succ k ih =>
      constructor
      · exact unbounded_choice_lt hC ih.2
      · unfold nested_unbounded_choice
        apply unbounded_choice_lt hD ih.1
  }

theorem int_two_club_unbounded (C D : Set Ordinal) (κ : Cardinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : Cardinal.aleph0 < κ) (hC: club_in C κ.ord) (hD : club_in D κ.ord) :
  unbounded_in (C ∩ D) κ.ord := by
  {
    · constructor
      · exact hC.1.1
      · intro a ha
        have hfg : ∃ f g : ℕ → Ordinal, ∀ n : ℕ, a < f 0 ∧  f (n) < g (n + 1) ∧
          g (n) < f (n + 1) ∧ f n ∈ C ∧ g n ∈ D ∧ f n < κ.ord := by
        {
          set f := fun n ↦ (nested_unbounded_choice hC.1 hD.1 ha n).1 ; use f
          set g := fun n ↦ (nested_unbounded_choice hC.1 hD.1 ha n).2 ; use g
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
        have hf02 : ∀ n : ℕ , f n < f (n + 2) := by
        {
          intro n
          have h₀₁ : f n < g (n + 1) := by
            specialize hfg n ; exact hfg.2.1
          have h₁₂ : g (n + 1) < f (n + 2) := by
            specialize hfg (n + 1) ; exact hfg.2.2.1
          exact lt_trans h₀₁ h₁₂
        } /-Make these lemmas, they are identical-/
        have hg02 : ∀ n : ℕ , g n < g (n + 2) := by
        {
          intro n
          have h₀₁ : g n < f (n + 1) := by
            specialize hfg n ; exact hfg.2.2.1
          have h₁₂ : f (n + 1) < g (n + 2) := by
            specialize hfg (n + 1) ; exact hfg.2.1
          exact lt_trans h₀₁ h₁₂
        }
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
        have hCα₁ : α = sSup (strict_Ordinal_res C α) := by
        {
          apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
          · exact Set.range_nonempty f
          · intro d hd
            obtain ⟨ y, hy ⟩ := hd ; rw [← hy]
            specialize hfg y
            apply le_csSup
            · exact strict_Ordinal_res_bdd C α
            · constructor
              · exact hfg.2.2.2.1 --f y ∈ C
              · apply lt_csSup_of_lt
                · exact Ordinal.bddAbove_range f
                · use y + 2
                · exact hf02 y
          · intro w hw
            apply exists_lt_of_lt_csSup
            · exact Set.range_nonempty f
            · have hw₂ : sSup (strict_Ordinal_res C α) ≤ α := by
                apply csSup_le'
                exact strict_Ordinal_res_bdd' C α
              exact LT.lt.trans_le hw hw₂
        }
        have hDα₁ : α = sSup (strict_Ordinal_res D α) := by
        {
          rw [this]
          apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
          · exact Set.range_nonempty g
          · intro d hd
            obtain ⟨ y, hy ⟩ := hd ; rw [← hy]
            specialize hfg y
            apply le_csSup
            · exact strict_Ordinal_res_bdd D (sSup (Set.range g))
            · constructor
              · exact hfg.2.2.2.2.1 --g y ∈ D
              · apply lt_csSup_of_lt
                · exact Ordinal.bddAbove_range g
                · use y + 2
                · exact hg02 y
          · intro w hw
            apply exists_lt_of_lt_csSup
            · exact Set.range_nonempty g
            · have hw₂ : sSup (strict_Ordinal_res D (sSup (Set.range g))) ≤ sSup (Set.range g) := by
                apply csSup_le'
                exact strict_Ordinal_res_bdd' D (sSup (Set.range g))
              exact LT.lt.trans_le hw hw₂
        }
        have h0α : f 0 < α := by
            apply lt_csSup_of_lt
            · exact Ordinal.bddAbove_range f
            · use 2
            · exact hf02 0
        have hCα₀ : Set.Nonempty (strict_Ordinal_res C α) := by
          exact nonempty_strict_res_of_sup h0α hCα₁.symm
        have hDα₀ : Set.Nonempty (strict_Ordinal_res D α) := by
          exact nonempty_strict_res_of_sup h0α (id hDα₁.symm)
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
      by_contra h'
      have hsCD' : Ordinal_res (C ∩ D) s = strict_Ordinal_res (C ∩ D) s := by
        exact res_eq_strict_res_iff.1 h'
      have hsb : s ≤ b := by
        apply csSup_le' ; exact strict_Ordinal_res_bdd' (C ∩ D) b
      have hsκ : s < κ.ord := by exact lt_of_le_of_lt hsb hb1
      have hsCD₀' : Set.Nonempty (Ordinal_res (C ∩ D) s) := by
      {
        obtain ⟨ c, hc ⟩ := hb2 ; use c ; constructor
        · exact hc.1
        · apply le_csSup ; exact strict_Ordinal_res_bdd (C ∩ D) b ; exact hc
      }
      have hsCD₀ : Set.Nonempty (strict_Ordinal_res (C ∩ D) s) := by
        rw [← hsCD'] ; exact hsCD₀'
      /-{
        obtain ⟨ c, hc ⟩ := hb2 ; use c ; constructor
        · exact hc.1
        · apply lt_csSup_of_lt
          · exact strict_Ordinal_res_bdd (C ∩ D) b
          · sorry
          · sorry
          · sorry
      }-/
      have hsCD : s = sSup (strict_Ordinal_res (C ∩ D) s) := by
      {
        refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
        · intro x hx ; use x
          rw [← hsCD']
          refine ⟨ ?_, Eq.le rfl  ⟩
          · refine ⟨ hx.1, ?_ ⟩
            apply le_csSup
            · exact strict_Ordinal_res_bdd (C ∩ D) b
            · exact hx
        · intro y hy ; use y
          refine ⟨ ⟨ hy.1, LT.lt.trans_le hy.2 hsb ⟩ , Eq.le rfl ⟩
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
        · have : sSup (strict_Ordinal_res (C ∩ D) s) ≤ sSup (strict_Ordinal_res C s) := by
          {
            apply csSup_le_csSup ; exact strict_Ordinal_res_bdd C s
            exact hsCD₀
            intro c hc ; constructor
            · exact hc.1.1
            · exact hc.2
          }
          exact Eq.trans_le hsCD this
      }
      have hsD : s = sSup (strict_Ordinal_res D s) := by
      {
        rw [←LE.le.ge_iff_eq]
        · apply csSup_le' ; exact strict_Ordinal_res_bdd' D s
        · have : sSup (strict_Ordinal_res (C ∩ D) s) ≤ sSup (strict_Ordinal_res D s) := by
          {
            apply csSup_le_csSup ; exact strict_Ordinal_res_bdd D s
            exact hsCD₀
            intro c hc ; constructor
            · exact hc.1.2
            · exact hc.2
          }
          exact Eq.trans_le hsCD this
      }
      have : s ∈ C ∩ D := by
        constructor
        · specialize hC2 s hsκ hsC₀ ; exact Set.mem_of_eq_of_mem hsC hC2
        · specialize hD2 s hsκ hsD₀ ; exact Set.mem_of_eq_of_mem hsD hD2
      exact h' this
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
      have h1 : Set.Iio (1 : Ordinal) = {0} := by sorry
      have : (⋂ i : Set.Iio (1 : Ordinal), C i) = C 0 := by
        sorry
      sorry
    · sorry
  · sorry
}

theorem diag_int_club_unbounded (κ : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (C : Ordinal → Set Ordinal) (hC : ∀ o : Ordinal, club_in (C o) κ.ord) :
  unbounded_in (diag_int κ C) κ.ord := by sorry

theorem diag_int_club (κ : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (C : Ordinal → Set Ordinal) (hC : ∀ o : Ordinal, club_in (C o) κ.ord) :
  club_in (diag_int κ C) κ.ord := by
{
  obtain hu := diag_int_club_unbounded κ hκ₁ hκ₂ C hC
  constructor
  · exact hu
  · intro b hb₁ hb₂
    set α := sSup (strict_Ordinal_res (diag_int κ C) b)
    by_contra h'
    have hαb : α ≤ b := by
      apply csSup_le hb₂
      intro c hc ; exact le_of_lt hc.2
    have hακ : α < κ.ord := by
      exact lt_of_le_of_lt hαb hb₁
    have : sSup (strict_Ordinal_res (diag_int κ C) b) ∉ strict_Ordinal_res (diag_int κ C) b := by
      {
        by_contra h''
        have : α ∈ diag_int κ C := by exact Set.mem_of_mem_inter_left h''
        exact h' this
      }
    have hα : sSup (strict_Ordinal_res (diag_int κ C) α) = α := by
      exact (strict_csSup_res_csSup_res this hb₂).symm
    have hα₂ : Set.Nonempty (strict_Ordinal_res (diag_int κ C) α) := by
      rw [(strict_res_csSup_res this hb₂).symm]
      exact hb₂
    have : ∃ θ : Ordinal, θ < α ∧ α ∉ C θ := by
    {
      by_contra h'₂ ; push_neg at h'₂
      have : α ∈ (diag_int κ C) := by constructor ; exact hακ ; exact h'₂
      exact h' this
    }
    obtain ⟨ θ₀, hθ₀₁, hθ₀₂ ⟩ := this
    by_cases Set.Nonempty (strict_Ordinal_res (C θ₀) α)
    · have hαθ₀ : sSup (strict_Ordinal_res (C θ₀) α) ∈ C θ₀ := by
        specialize hC θ₀ ; unfold club_in at hC ; obtain ⟨ _, hC₂ ⟩ := hC
        specialize hC₂ α hακ h ; exact hC₂
      have hθ₀α : sSup (strict_Ordinal_res (C θ₀) α) < α := by
      {
        by_contra h'₂ ; push_neg at h'₂
        have : α = sSup (strict_Ordinal_res (C θ₀) α) := by
          apply LE.le.antisymm h'₂
          apply csSup_le h ; intro d hd ; exact le_of_lt hd.2
        have hαθ₀' : α ∈ C θ₀ := by
          exact Set.mem_of_eq_of_mem this hαθ₀
        exact hθ₀₂ hαθ₀'
      }
      have hv : ∃ v : Ordinal,
        v ∈ (diag_int κ C) ∧ θ₀ < v ∧ v < α ∧ sSup (strict_Ordinal_res (C θ₀) α) < v := by
        {
          have h₄ : Set.Nonempty {x ∈ (strict_Ordinal_res (diag_int κ C) α) |
            (max (sSup (strict_Ordinal_res (C θ₀) α)) θ₀) < x} := by
          {
            refine nonempty_lbd_of_sup (strict_Ordinal_res (diag_int κ C) α)
              (max (sSup (strict_Ordinal_res (C θ₀) α)) θ₀) hα₂ ?_
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
        · exact strict_Ordinal_res_bdd (C θ₀) α
      · specialize hv' θ₀ hv₂
        exact hvθ₀ hv'
    · have hv : ∃ v : Ordinal, v ∈ (diag_int κ C) ∧ θ₀ < v ∧ v < α := by
        {
          have h₄ : Set.Nonempty {x ∈ (strict_Ordinal_res (diag_int κ C) α) | θ₀ < x} := by
            refine nonempty_lbd_of_sup (strict_Ordinal_res (diag_int κ C) α) θ₀ hα₂ ?_
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
      · have : v ∈ (strict_Ordinal_res (C θ₀) α) := by
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
        · apply (sub_Ordinal_iff_strict_res_eq C (Cardinal.ord κ)).2
          intro c hc
          simp at hc ; rw [diag_int] at hc ; simp at hc ;  exact hc.1
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


• Do the res_eq_strict_res theorem with the ' assumption
• make some things in theorems implicit
• lemma : If sSup is not in the set, then there is a strictly smaller element in the set
  Fodor's lemma holds for this one as well
• Find a way to construct the f and g in the two set intersection proof
• Get induction to work for int_lt_card_club
• diag_int_club unboundedness proof
• cleanup part 1 : Nested constructors
• cleanup part 2 : Every definition should be followed by some obvious lemmas
• cleanup part 3 : Naming
 -/
