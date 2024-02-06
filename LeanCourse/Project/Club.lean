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
      exact ⟨ hx.1, le_csSup (Ordinal_res_bdd C o) hx ⟩
    · intro hx
      constructor
      · exact hx.1
      · have : s ≤ o := by
          apply csSup_le' (Ordinal_res_bdd' C o)
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
        apply le_csSup (strict_Ordinal_res_bdd C o)
        exact hx
      }
      rw [hox] at hCo₁
      exact hCo₁ hx
    · intro ⟨ hx₁, hx₂ ⟩
      refine ⟨ hx₁, ?_ ⟩
      have : sSup (strict_Ordinal_res C o) ≤ o := by
      {
        apply csSup_le hCo₂
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

/--A stationary set is a subset of an ordinal that intersects every club sets.-/
def stationary_in (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, (sub_Ordinal C o ∧ club_in C o) → Set.Nonempty (S ∩ C)

/--The diagonal intersection of a family.-/
def diag_int (o : Ordinal) (C : Ordinal → Set Ordinal) : Set Ordinal :=
  {β : Ordinal | β < o ∧ ∀ θ : Ordinal, θ < β → β ∈ C θ}

lemma diag_int_of_int (o : Ordinal) (C : Ordinal → Set Ordinal) :
  diag_int o C = diag_int o (fun a ↦ (⋂ i : Set.Iic a, C (i : Ordinal))) := by
  {
    ext x ; constructor
    · intro ⟨ hx₁, hx₂ ⟩
      refine ⟨ hx₁, ?_ ⟩
      intro θ hθ
      rw [@Set.mem_iInter] ; intro i
      exact hx₂ (↑i) (LT.lt.trans_le' hθ i.2)
    · intro ⟨ hx₁, hx₂ ⟩
      refine ⟨ hx₁, ?_ ⟩
      intro θ hθ
      refine hx₂ θ hθ (C θ) ?_
      simp [Set.iInter_coe_set]
      use θ
  }

/--A regressive function in the context opf ordinals.-/
def Ord_fun_regressive (C : Set Ordinal) (f : Ordinal → Ordinal) : Prop :=
  ∀ c : Ordinal, c ∈ C → f c < c

noncomputable instance Decidable_unbounded {C : Set Ordinal} {o : Ordinal} : Decidable (unbounded_in C o) := by
  exact Classical.dec (unbounded_in C o)

noncomputable def unbounded_choice (C : Set Ordinal) (o : Ordinal) (a : Ordinal) : Ordinal :=
    if hC: (unbounded_in C o) then
      if ha : a < o then Exists.choose (hC.2 a ha)
      else 0
    else 0

lemma unbounded_choice_lt {C : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (ha : a < o) : unbounded_choice C o a < o := by
    unfold unbounded_choice
    simp [hC, ha]
    exact (Exists.choose_spec (hC.2 a ha)).1

lemma unbounded_choice_gt {C : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (ha : a < o) : a < unbounded_choice C o a := by
    unfold unbounded_choice
    simp [hC, ha]
    exact (Exists.choose_spec (hC.2 a ha)).2.2

lemma unbounded_choice_in {C : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (ha : a < o) : (unbounded_choice C o a) ∈ C := by
    unfold unbounded_choice
    simp [hC, ha]
    exact (Exists.choose_spec (hC.2 a ha)).2.1

noncomputable def nested_unbounded_choice {C D : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (hD : unbounded_in D o) (ha : a < o) : ℕ → Ordinal × Ordinal
  | 0 => (unbounded_choice C o a, unbounded_choice D o a)
  | n + 1 => (unbounded_choice C o (nested_unbounded_choice hC hD ha n).2,
    unbounded_choice D o (nested_unbounded_choice hC hD ha n).1)

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
      · apply unbounded_choice_lt hD ih.1
  }

lemma nested_unbounded_choice_gt_zero {C D : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (hD : unbounded_in D o) (ha : a < o) :
  a < (nested_unbounded_choice hC hD ha 0).1 ∧ a < (nested_unbounded_choice hC hD ha 0).2:= by
      exact ⟨ unbounded_choice_gt hC ha, unbounded_choice_gt hD ha ⟩

lemma nested_unbounded_choice_in {C D : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (hD : unbounded_in D o) (ha : a < o) (n : ℕ) :
  (nested_unbounded_choice hC hD ha n).1 ∈ C ∧ (nested_unbounded_choice hC hD ha n).2 ∈ D := by
  {
    induction n
    case zero =>
      unfold nested_unbounded_choice
      constructor
      · exact unbounded_choice_in hC ha
      · exact unbounded_choice_in hD ha
    case succ k _ =>
      constructor
      · exact unbounded_choice_in hC (nested_unbounded_choice_lt hC hD ha k).2
      · exact unbounded_choice_in hD (nested_unbounded_choice_lt hC hD ha k).1
  }

lemma nested_unbounded_choice_alt {C D : Set Ordinal} {o a: Ordinal}
  (hC: unbounded_in C o) (hD : unbounded_in D o) (ha : a < o) (n : ℕ) :
  (nested_unbounded_choice hC hD ha n).1 < (nested_unbounded_choice hC hD ha (n + 1)).2
  ∧ (nested_unbounded_choice hC hD ha n).2 < (nested_unbounded_choice hC hD ha (n + 1)).1:= by
  {
    induction n
    case zero =>
      unfold nested_unbounded_choice
      constructor
      · exact unbounded_choice_gt hD (unbounded_choice_lt hC ha)
      · exact unbounded_choice_gt hC (unbounded_choice_lt hD ha)
    case succ k _ =>
      unfold nested_unbounded_choice
      constructor
      · exact unbounded_choice_gt hD (unbounded_choice_lt hC (nested_unbounded_choice_lt hC hD ha k).2)
      · exact unbounded_choice_gt hC (unbounded_choice_lt hD (nested_unbounded_choice_lt hC hD ha k).1)
  }

/-Variation of the other choice function Note the order swap between a and b-/
noncomputable def diag_unbounded_choice (C : Ordinal → Set Ordinal) (a b : Ordinal) : ℕ → Ordinal
  | 0 => unbounded_choice (C 0) b a
  | n + 1 => unbounded_choice (C (diag_unbounded_choice C a b n)) b (diag_unbounded_choice C a b n)

lemma diag_unbounded_choice_lt (C : Ordinal → Set Ordinal) (a b : Ordinal)
  (hab : a < b) (h₀ : 0 < b) (hC : ∀ o : Ordinal, o < b → unbounded_in (C o) b) :
    ∀ n : ℕ, diag_unbounded_choice C a b n < b := by
  {
    intro n
    induction n
    case zero =>
      unfold diag_unbounded_choice
      specialize hC 0 h₀
      exact unbounded_choice_lt hC hab
    case succ k ih =>
      unfold diag_unbounded_choice
      specialize hC (diag_unbounded_choice C a b k) ih
      apply unbounded_choice_lt hC ih
  }

lemma diag_unbounded_choice_gt (C : Ordinal → Set Ordinal) (a b : Ordinal)
  (hab : a < b) (h₀ : 0 < b) (hC : ∀ o : Ordinal, o < b → unbounded_in (C o) b) :
    ∀ n : ℕ, a < diag_unbounded_choice C a b n := by
  {
    intro n
    induction n
    case zero =>
      unfold diag_unbounded_choice
      specialize hC 0 h₀
      exact unbounded_choice_gt hC hab
    case succ k ih =>
      unfold diag_unbounded_choice
      obtain hC₂ := hC (diag_unbounded_choice C a b k) (diag_unbounded_choice_lt C a b hab h₀ hC k)
      obtain h₂ := unbounded_choice_gt hC₂ (diag_unbounded_choice_lt C a b hab h₀ hC k)
      exact gt_trans h₂ ih
  }

lemma diag_unbounded_choice_in0 (C : Ordinal → Set Ordinal) (a b : Ordinal)
  (hab : a < b) (h₀ : 0 < b) (hC : ∀ o : Ordinal, o < b → unbounded_in (C o) b) :
    diag_unbounded_choice C a b 0 ∈ (C 0) := by
  exact unbounded_choice_in (hC 0 h₀) hab

lemma diag_unbounded_choice_in (C : Ordinal → Set Ordinal) (a b : Ordinal)
  (hab : a < b) (h₀ : 0 < b) (hC : ∀ o : Ordinal, o < b → unbounded_in (C o) b) :
    ∀ n : ℕ, diag_unbounded_choice C a b (n + 1) ∈ (C (diag_unbounded_choice C a b n)) := by
  intro n
  induction n
  case zero =>
    unfold diag_unbounded_choice ; unfold diag_unbounded_choice
    refine unbounded_choice_in ?_ (unbounded_choice_lt (hC 0 h₀) hab)
    apply hC
    exact unbounded_choice_lt (hC 0 h₀) hab
  case succ k _ =>
    unfold diag_unbounded_choice
    apply unbounded_choice_in
    apply hC
    exact diag_unbounded_choice_lt C a b hab h₀ hC (k + 1)
    exact diag_unbounded_choice_lt C a b hab h₀ hC (k + 1)

lemma diag_unbounded_choice_increasing (C : Ordinal → Set Ordinal) (a b : Ordinal)
  (hab : a < b) (h₀ : 0 < b) (hC : ∀ o : Ordinal, o < b → unbounded_in (C o) b) :
    ∀ n : ℕ, diag_unbounded_choice C a b n < diag_unbounded_choice C a b (n + 1) := by
  intro n
  induction n
  case zero =>
    unfold diag_unbounded_choice ; unfold diag_unbounded_choice
    apply unbounded_choice_gt
    · exact hC (unbounded_choice (C 0) b a) (unbounded_choice_lt (hC 0 h₀) hab)
    · exact unbounded_choice_lt (hC 0 h₀) hab
  case succ k _ =>
    unfold diag_unbounded_choice
    apply unbounded_choice_gt
    apply hC
    · exact diag_unbounded_choice_lt C a b hab h₀ hC (k + 1)
    · apply unbounded_choice_lt
      · apply hC ; exact diag_unbounded_choice_lt C a b hab h₀ hC k
      · exact diag_unbounded_choice_lt C a b hab h₀ hC k

noncomputable def int_unbounded_choice (C : Ordinal → Set Ordinal) (a b c: Ordinal) : (Set.Iic c) → Ordinal := by
{
  intro ⟨ x, hx ⟩
  induction x using Ordinal.limitRecOn
  case H₁
  -- induction c using Ordinal.limitRecOn
  -- case H₁ =>
  --   intro x
  --   use unbounded_choice (C 0) b a
  -- case H₂ d f =>
  --   intro ⟨ x, hx ⟩
  --   simp at hx
  --   rw [@Order.le_succ_iff_eq_or_le] at hx
  --   by_cases hx₁ : x ≤ d --Why can't I separate hx into two cases immediately?
  --   · use f ⟨ x, hx₁ ⟩
  --   · rw [propext (or_iff_left hx₁)] at hx
  --     if hC : unbounded_in (⋂ i : (Set.Iic d), C i) b then
  --       use unbounded_choice (⋂ i : (Set.Iic d), C i) b (int_unbounded_choice C a b d ⟨ d, Set.right_mem_Iic ⟩)
  --     else use 0
  -- case H₃ d hd f =>
  --   intro ⟨ x, hx ⟩
  --   simp at hx
  --   rw [@le_iff_lt_or_eq] at hx
  --   by_cases hx₁ : x < d
  --   · use f x hx₁ ⟨ x, Set.right_mem_Iic ⟩
  --   · rw [propext (or_iff_right hx₁)] at hx ; clear hx₁
  --     if hC : unbounded_in (⋂ i : (Set.Iio d), C i) b then
  --       use unbounded_choice (⋂ i : (Set.Iio d), C i) b (int_unbounded_choice C a b d ⟨ d, Set.right_mem_Iic ⟩)
  --     else use 0
}
