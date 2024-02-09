import LeanCourse.Common
import Mathlib.Logic.Nonempty
import Mathlib.Init.Classical
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import LeanCourse.Project.Club

theorem int_two_club_unbounded (C D : Set Ordinal) (o : Ordinal)
  (hocof : Cardinal.aleph0 < o.cof) (hC: club_in C o) (hD : club_in D o) :
  unbounded_in (C ∩ D) o := by
  {
    · constructor
      · exact hC.1.1
      · intro a ha
        have hfg : ∃ f g : ℕ → Ordinal, ∀ n : ℕ, a < f 0 ∧  f (n) < g (n + 1) ∧
          g (n) < f (n + 1) ∧ f n ∈ C ∧ g n ∈ D ∧ f n < o := by
        {
          set f := fun n ↦ (nested_unbounded_choice hC.1 hD.1 ha n).1 ; use f
          set g := fun n ↦ (nested_unbounded_choice hC.1 hD.1 ha n).2 ; use g
          intro n
          refine ⟨ ?_, ?_, ?_, ?_, ?_, (nested_unbounded_choice_lt hC.1 hD.1 ha n).1⟩
          · exact (nested_unbounded_choice_gt_zero hC.1 hD.1 ha).1
          · exact (nested_unbounded_choice_alt hC.1 hD.1 ha n).1
          · exact (nested_unbounded_choice_alt hC.1 hD.1 ha n).2
          · exact (nested_unbounded_choice_in hC.1 hD.1 ha n).1
          · exact (nested_unbounded_choice_in hC.1 hD.1 ha n).2
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
        } /-Can I make these one conjunction provable by a previous unbounded_choice lemma?-/
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
              obtain h := hfg.2.1 --f n < g (n + 1)
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
        have hα : α < o := by
        {
          have hn : ∀ n : ℕ, f n < o := by
            intro n ; specialize hfg n
            exact hfg.2.2.2.2.2 -- f n < o
          apply Ordinal.sup_lt_ord_lift hocof hn
        }
        have hCα₁ : α = sSup (strict_Ordinal_res C α) := by
        {
          apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
          · exact Set.range_nonempty f
          · intro d hd
            obtain ⟨ y, hy ⟩ := hd ; rw [← hy]
            specialize hfg y
            apply le_csSup (strict_Ordinal_res_bdd C α)
            constructor
            · exact hfg.2.2.2.1 --f y ∈ C
            · apply lt_csSup_of_lt
              · exact Ordinal.bddAbove_range f
              · use y + 2
              · exact hf02 y
          · intro w hw
            apply exists_lt_of_lt_csSup (Set.range_nonempty f)
            have hw₂ : sSup (strict_Ordinal_res C α) ≤ α := by
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
        } /-The previous steps could be a lemma-/
        have h0α : f 0 < α := by
            apply lt_csSup_of_lt (Ordinal.bddAbove_range f)
            use 2
            exact hf02 0
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
          apply le_csSup (Ordinal.bddAbove_range f) ; use 0
        have hf0' : a < f 0 := by specialize hfg 0 ; exact hfg.1
        exact LT.lt.trans_le hf0' hf0
  }

theorem int_two_club (C D : Set Ordinal) (o : Ordinal)
  (hκ : Cardinal.aleph0 < o.cof) (hC: club_in C o) (hD : club_in D o) :
    club_in (C ∩ D) o := by
  {
    obtain hCD := int_two_club_unbounded C D o hκ hC hD
    constructor
    · exact hCD
    · obtain ⟨ _ , hC2 ⟩ := hC ; obtain ⟨ _, hD2 ⟩ := hD
      intro b hb1 hb2
      set s := sSup (strict_Ordinal_res (C ∩ D) b)
      by_contra h'
      have hsCD' : Ordinal_res (C ∩ D) s = strict_Ordinal_res (C ∩ D) s := by
        exact res_eq_strict_res_iff.1 h'
      have hsb : s ≤ b := by
        apply csSup_le' ; exact strict_Ordinal_res_bdd' (C ∩ D) b
      have hsκ : s < o := by exact lt_of_le_of_lt hsb hb1
      have hsCD₀' : Set.Nonempty (Ordinal_res (C ∩ D) s) := by
      {
        obtain ⟨ c, hc ⟩ := hb2 ; use c ; constructor
        · exact hc.1
        · apply le_csSup (strict_Ordinal_res_bdd (C ∩ D) b) ; exact hc
      }
      have hsCD₀ : Set.Nonempty (strict_Ordinal_res (C ∩ D) s) := by
        rw [← hsCD'] ; exact hsCD₀'
      have hsCD : s = sSup (strict_Ordinal_res (C ∩ D) s) := by
      {
        refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
        · intro x hx ; use x
          rw [← hsCD']
          refine ⟨ ?_, Eq.le rfl  ⟩
          · refine ⟨ hx.1, ?_ ⟩
            apply le_csSup (strict_Ordinal_res_bdd (C ∩ D) b)
            exact hx
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
        · apply csSup_le' (strict_Ordinal_res_bdd' C s)
        · have : sSup (strict_Ordinal_res (C ∩ D) s) ≤ sSup (strict_Ordinal_res C s) := by
          {
            apply csSup_le_csSup (strict_Ordinal_res_bdd C s) hsCD₀
            intro c hc ;
            exact ⟨ hc.1.1, hc.2 ⟩
          }
          exact Eq.trans_le hsCD this
      }
      have hsD : s = sSup (strict_Ordinal_res D s) := by
      {
        rw [←LE.le.ge_iff_eq]
        · apply csSup_le' (strict_Ordinal_res_bdd' D s)
        · have : sSup (strict_Ordinal_res (C ∩ D) s) ≤ sSup (strict_Ordinal_res D s) := by
          {
            apply csSup_le_csSup (strict_Ordinal_res_bdd D s)
            exact hsCD₀
            intro c hc
            exact ⟨ hc.1.2, hc.2 ⟩
          }
          exact Eq.trans_le hsCD this
      }
      have : s ∈ C ∩ D := by
        constructor
        · specialize hC2 s hsκ hsC₀ ; exact Set.mem_of_eq_of_mem hsC hC2
        · specialize hD2 s hsκ hsD₀ ; exact Set.mem_of_eq_of_mem hsD hD2
      exact h' this
  }

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
      by_cases 0 <d
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
        · exact h
      · exact hC d (Order.lt_succ d)
      rw [@not_lt] at h ; rw [@Ordinal.le_zero] at h
      have : ⋂ i : Set.Iio (Order.succ d), (C i) = C 0 := by
        ext x ; constructor
        · intro hx ; simp at hx ; rw [h] at hx
          apply hx ; rfl
        · intro hx ; simp ; intro i hi ; rw [h] at hi
          have : i = 0 := by exact Ordinal.le_zero.mp hi
          rw [this] ; exact hx
      rw [this] ; exact hC 0 nontriv
    case H₃ d hd₁ _ =>
      rw [← @Cardinal.lt_ord] at hlκ
      constructor
      · refine ⟨ Cardinal.ord_isLimit (Cardinal.IsRegular.aleph0_le hκ₁), ?_ ⟩
        intro a ha
        set f : (o : Ordinal) → (o < d) → Ordinal := fun o _ ↦ long_unbounded_choice C a κ.ord o
        set s := Ordinal.bsup.{u_1, 0} d f
        use s
        have hfs : ∀ (o : Ordinal), (ho : o < d) → f o ho < s := by
        {
          intro o ho
          apply lt_csSup_of_lt
          · exact Ordinal.bddAbove_range.{_, 0} (Ordinal.familyOfBFamily d f)
          · simp ; use Order.succ o
            have h1d := Ordinal.IsLimit.succ_lt hd₁ ho
            use h1d
          · simp
            apply long_unbounded_choice_increasing
            · exact hκ₁
            · exact hκ₂
            · exact gt_trans hlκ ho
            · have : Order.succ o < d := by exact Ordinal.IsLimit.succ_lt hd₁ ho
              exact gt_trans hlκ this
            · exact Order.lt_succ o
            · exact ha
            · intro j hj
              specialize hC j ?_
              · rw [@Order.le_succ_iff_eq_or_le] at hj
                obtain hj₁|hj₂ := hj
                · rw [hj₁]
                  rw [propext (Ordinal.succ_lt_of_isLimit hd₁)] ; exact ho
                · exact lt_of_le_of_lt hj₂ ho
              · exact hC.1
        }
        have hfκ : ∀ x : Ordinal, (hxd : x < d) → f x hxd < κ.ord := by
        {
          intro x hxd
          simp
          apply long_unbounded_choice_lt
          · exact hκ₁
          · exact hκ₂
          · exact gt_trans hlκ hxd
          · exact ha
          · intro j hj
            specialize hC j ?_
            exact lt_of_le_of_lt hj hxd
            exact hC.1
        }
        refine ⟨ Cardinal.bsup_lt_ord_of_isRegular hκ₁ (Cardinal.lt_ord.1 hlκ) hfκ, ?_, ?_ ⟩
        · intro D ⟨ ⟨ i, hi₁ ⟩, hi₂ ⟩ ; simp at hi₂ ; simp at hi₁ ; rw [← hi₂]
          have hs : s = sSup (strict_Ordinal_res (C i) s) := by
          {
            apply csSup_eq_csSup_of_forall_exists_le
            · intro x hx ; simp at hx
              obtain ⟨ j, hjd, hj ⟩ := hx ; simp at hj
              have hijd : Order.succ (max i j) < d := by
                  rw [propext (Ordinal.succ_lt_of_isLimit hd₁), @max_lt_iff]
                  exact ⟨ hi₁, hjd ⟩
              use f (Order.succ (max i j)) hijd
              constructor
              · constructor
                · simp
                  have : f (Order.succ (max i j)) hijd ∈ C (Order.succ (max i j)) := by
                    apply long_unbounded_choice_in
                    · exact hκ₁
                    · exact hκ₂
                    · exact gt_trans hlκ hijd
                    · exact ha
                    · intro m hm
                      specialize hC m ?_
                      · rw [@Order.le_succ_iff_eq_or_le] at hm ; obtain hm₁|hm₂ := hm
                        · rw [hm₁, propext (Ordinal.succ_lt_of_isLimit hd₁)]
                          exact (Ordinal.succ_lt_of_isLimit hd₁).mp hijd
                        · have : max i j < d := by
                            exact (Ordinal.succ_lt_of_isLimit hd₁).mp hijd
                          exact lt_of_le_of_lt hm₂ this
                      exact hC.1
                  have hijsub : C (Order.succ (max i j)) ⊆ C i := by
                    apply hCsub
                    rw [@Order.lt_succ_iff] ; exact le_max_left i j
                  exact hijsub this
                · apply hfs ; exact hijd
              · rw [← hj] ; simp
                apply le_of_lt
                apply long_unbounded_choice_increasing
                · exact hκ₁
                · exact hκ₂
                · exact gt_trans hlκ hjd
                · exact gt_trans hlκ hijd
                · rw [@Order.lt_succ_iff] ; exact le_max_right i j
                · exact ha
                · intro m hm
                  specialize hC m ?_
                  · rw [@Order.le_succ_iff_eq_or_le] at hm ; obtain hm₁|hm₂ := hm
                    · rw [hm₁, propext (Ordinal.succ_lt_of_isLimit hd₁)]
                      exact (Ordinal.succ_lt_of_isLimit hd₁).mp hijd
                    · have : max i j < d := by
                        exact (Ordinal.succ_lt_of_isLimit hd₁).mp hijd
                      exact lt_of_le_of_lt hm₂ this
                  exact hC.1
            · intro y ⟨ _, hy₂ ⟩
              apply exists_lt_of_lt_csSup at hy₂
              obtain ⟨ x, hx ⟩ := hy₂
              use x ; refine ⟨ hx.1, le_of_lt hx.2 ⟩
              simp ; use f i hi₁
              use i
          }
          rw [hs]
          obtain hCi := hC i hi₁
          apply hCi.2
          exact Cardinal.bsup_lt_ord_of_isRegular hκ₁ (Cardinal.lt_ord.1 hlκ) hfκ
          refine @nonempty_strict_res_of_sup (C i) s (f 0 ?_) ?_ ?_
          · exact nontriv
          · exact hfs 0 nontriv
          · exact hs.symm
        · apply lt_csSup_of_lt
          exact Ordinal.bddAbove_range.{_, 0} (Ordinal.familyOfBFamily d f)
          simp
          use 0
          unfold long_unbounded_choice ; simp
          apply @unbounded_choice_gt (C 0) κ.ord a
          · exact (hC 0 nontriv).1
          · exact ha
      · intro b hb₁ hb₂
        intro D ⟨ ⟨ j, hj ⟩ , hD ⟩ ; simp at hD ; rw [← hD] ; simp at hj
        obtain ⟨ ⟨ _, _ ⟩ , hCj₂ ⟩ := hC j hj
        set s := sSup (strict_Ordinal_res (⋂ i : (Set.Iio d), C i) b)
        by_contra h'
        have h'' : s ∈ C j := by
          have hs : s = sSup (strict_Ordinal_res (C j) s) := by
          {
            apply csSup_eq_csSup_of_forall_exists_le
            · intro x ⟨ hx₁, hx₂ ⟩
              simp at hx₁
              obtain hxj := hx₁ j hj
              obtain hCjs := res_eq_strict_res_iff.1 h'
              rw [← hCjs]
              use x ; refine ⟨ ⟨ hxj, ?_ ⟩ , Eq.le rfl ⟩
              apply le_csSup (strict_Ordinal_res_bdd (⋂ i : (Set.Iio d), C i) b)
              refine ⟨ ?_, hx₂ ⟩
              simp ; exact hx₁
            · intro y ⟨ _, hy₂ ⟩
              obtain ⟨ z, hz₁, hz₂ ⟩ := exists_lt_of_lt_csSup' hy₂
              use z ; exact ⟨ hz₁, le_of_lt hz₂ ⟩
          }
          rw [hs]
          apply hCj₂
          · obtain hsb := csSup_le' (strict_Ordinal_res_bdd' (⋂ i : (Set.Iio d), C i) b)
            exact lt_of_le_of_lt hsb hb₁
          · obtain ⟨ c, ⟨ hc₁, hc₂ ⟩ ⟩ := hb₂
            simp at hc₁
            use c ; refine ⟨ hc₁ j hj, ?_ ⟩
            suffices hcs : c ≤ s by
              by_contra hcs' ; push_neg at hcs'
              rw [propext (LE.le.ge_iff_eq hcs')] at hcs
              specialize hc₁ j hj
              rw [← hcs] at hc₁
              exact h' hc₁
            apply le_csSup (strict_Ordinal_res_bdd (⋂ i : (Set.Iio d), C i) b)
            constructor
            · simp ; exact hc₁
            · exact hc₂
        exact h' h''
  }

theorem int_lt_card_club {κ : Cardinal} (l : Ordinal) (hκ₁ : κ.IsRegular)
  (hκ₂ : Cardinal.aleph0 < κ) (hlκ : l.card < κ) (C : Ordinal → Set Ordinal)
  (hC : ∀ i : Ordinal, i < κ.ord → club_in (C i) κ.ord) :
    club_in (⋂ i : Set.Iic l, (C i)) κ.ord := by
{
  induction l using Ordinal.limitRecOn
  case H₁ =>
    have h : (⋂ i : Set.Iic (0 : Ordinal), (C i)) = C 0 := by --there has to be a simpler way to do this
    {
      ext x ; constructor
      · intro hx
        simp [Set.iInter_coe_set] at hx
        exact hx
      · intro hx
        simp [Set.iInter_coe_set]
        exact hx
    }
    rw [h] ; exact hC 0 (Cardinal.IsRegular.ord_pos hκ₁)
  case H₂ d hd =>
    have : (⋂ i : Set.Iic (Order.succ d), (C i)) = --Make this a lemma
      (⋂ i : Set.Iic d, (C i)) ∩ (C (Order.succ d)) :=by
      {
        ext x ; constructor
        · intro hx ; simp [Set.iInter_coe_set] at *
          constructor
          · intro i hi
            refine hx i ?_
            apply le_of_lt ; exact Order.lt_succ_iff.mpr hi
          · refine hx (Order.succ d) ?_
            exact Eq.le rfl
        · intro hx ; simp [Set.iInter_coe_set] at * ; obtain ⟨ hx₁, hx₂ ⟩ := hx
          intro i hi
          rw [@Order.le_succ_iff_eq_or_le] at hi
          obtain hi₁|hi₂ := hi
          · rw [← hi₁] at hx₂ ; exact hx₂
          · exact hx₁ i hi₂
      }
    rw [this]
    apply int_two_club
    · rw [Cardinal.IsRegular.cof_eq hκ₁] ; exact hκ₂
    · apply hd
      rw [Ordinal.card_succ] at hlκ
      have hd1 : d.card ≤ d.card + 1 := by exact le_self_add
      exact lt_of_le_of_lt hd1 hlκ
    rw [← @Cardinal.lt_ord] at hlκ
    refine  hC (Order.succ d) hlκ
  case H₃ d hd₁ hd₂ =>
    set int : Ordinal → Set Ordinal := fun o ↦ ⋂ j : (Set.Iic o), (C j)
    have hint : ⋂ i : (Set.Iio d), (C i) = ⋂ i : (Set.Iio d), (int i) := by --Make this a lemma
    {
      ext x ; constructor
      · intro hx ; simp at hx
        intro D ⟨ ⟨ j, hj ⟩, hDj ⟩ ; simp at hDj
        rw [← hDj]
        rw [@Set.mem_iInter₂]
        intro i hi
        apply hx
        exact lt_of_le_of_lt hi hj
      · intro hx ; simp at *
        intro i hi
        apply hx i hi i ; exact Eq.le rfl
    }
    have := int_Iic C d
    rw [this] ; apply int_two_club ; clear this
    · rw [Cardinal.IsRegular.cof_eq hκ₁] ; exact hκ₂
    · rw [hint]
      apply int_lt_card_sub_club d hκ₁ hκ₂ hlκ
      · intro i hi
        simp
        specialize hd₂ i hi ?_
        · rw [← @Cardinal.lt_ord] at * ; exact lt_trans hi hlκ
        simp at hd₂ ; exact hd₂
      · intro p q hpq x hx
        simp ; simp at hx
        intro i hi
        have hiq : i ≤ q := by
          apply le_of_lt ; exact lt_of_le_of_lt hi hpq
        exact hx i hiq
      · exact Ordinal.IsLimit.pos hd₁
    · refine hC d ?_
      exact Cardinal.lt_ord.mpr hlκ
}

theorem diag_int_club_sub_unbounded {o : Ordinal} (hocof : Cardinal.aleph0 < o.cof)
  (C : Ordinal → Set Ordinal) (hC : ∀ d : Ordinal, d < o → club_in (C d) o)
  (hCsub : ∀ a d : Ordinal, a < d → C d ⊆ C a) :
    unbounded_in (diag_int o C) o := by
  {
    have hnat : 0 < o := by
    {
      by_contra h' ; push_neg at h'
      have : o.cof = 0 := by
        exact Ordinal.cof_eq_zero.mpr (Ordinal.le_zero.mp h')
      rw [this] at hocof
      simp at hocof
    }
    have hC₁ : ∀ d : Ordinal, d < o → unbounded_in (C d) o := by
      intro d hd ; exact (hC d hd).1
    refine ⟨ (hC 0 hnat).1.1, ?_ ⟩
    intro a ha
    have : ∃ f : ℕ → Ordinal, a < f 0  ∧
      ∀ n, f (n + 1) ∈ C (f n) ∧ f n < f (n + 1) ∧ f n < o := by
    {
      use fun n ↦ diag_unbounded_choice C a o n
      refine ⟨ (diag_unbounded_choice_gt C a o ha hnat hC₁ 0),
        ?_ ⟩
      intro n
      refine ⟨ (diag_unbounded_choice_in C a o ha hnat hC₁ n),
        (diag_unbounded_choice_increasing C a o ha hnat hC₁ n),
        (diag_unbounded_choice_lt C a o ha hnat hC₁ n) ⟩
    }
    obtain ⟨ f, hf₁, hf₂ ⟩ := this
    have hfinc : ∀ n m : ℕ, n < m → f n < f m := by --Make this a lemma
    {
      intro n m hnm
      induction m
      case zero =>
        exfalso
        exact Nat.not_succ_le_zero n hnm
      case succ k ih =>
        have : f k  < f (k + 1) := by
          specialize hf₂ k ; exact hf₂.2.1
        by_cases k ≤ n
        · have hnk : n = k := by
            rw [@Nat.lt_succ] at hnm ; exact Nat.le_antisymm hnm h
          rw [hnk] ; exact this
        · push_neg at h ; specialize ih h
          exact lt_trans ih this
    }
    have hfC : ∀ n m : ℕ, n < m → f m ∈ C (f n) := by /-Make this a lemma too.
    Actually it would probably be possible to have this and the previous one as one lemma.-/
    {
      intro n m hnm
      induction m
      case zero =>
        exfalso ; exact Nat.not_succ_le_zero n hnm
      case succ k ih =>
        have : f (k + 1) ∈ C (f k) := by
          specialize hf₂ k ; exact hf₂.1
        by_cases k ≤ n
        · have hnk : n = k := by
            rw [@Nat.lt_succ] at hnm ; exact Nat.le_antisymm hnm h
          rw [hnk] ; exact this
        · push_neg at h ; specialize ih h
          exact hCsub (f n) (f k) (hfinc n k h) this
    }
    set b := Ordinal.sup f ; use b
    have hfo : ∀ n, f n < o := by
      intro n ; specialize hf₂ n ; exact hf₂.2.2
    have hfb : ∀ n, f n < b := by /-Make this a lemma-/
    {
      intro n ; specialize hf₂ n
      apply lt_csSup_of_lt (Ordinal.bddAbove_range f)
      · use (n +1)
      · exact hf₂.2.1
    }
    obtain hbκ := Ordinal.sup_lt_ord_lift hocof hfo
    refine ⟨ hbκ, ?_ ⟩
    constructor
    · refine ⟨ hbκ, ?_ ⟩
      intro θ hθ
      obtain ⟨ n, hn ⟩ := Ordinal.lt_sup.mp hθ
      obtain hfCn := hfC n
      have hCb : b ∈ C (f n) := by
      {
        specialize hC (f n) (hfo n)
        obtain ⟨ _, hC₂ ⟩ := hC
        specialize hC₂ b hbκ ?_
        · use f (n + 1)
          refine ⟨ hfCn (n + 1) (Nat.lt.base n), ?_ ⟩
          exact hfb (n + 1)
        have : sSup (strict_Ordinal_res (C (f n)) b) = b := by
        {
          apply csSup_eq_csSup_of_forall_exists_le
          · intro x ⟨ _, hx₂ ⟩
            obtain ⟨ m, hm ⟩ := Ordinal.lt_sup.mp hx₂ ; use f m
            refine ⟨ ?_, le_of_lt hm ⟩ ; use m
          · intro y ⟨ k, hk ⟩
            use f ((max n k) + 1)
            refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩
            · refine hfCn ((max n k) + 1) ?_ ;
              rw [@Nat.lt_succ] ; exact Nat.le_max_left n k
            · exact hfb (max n k + 1)
            · apply le_of_lt ; rw [← hk]
              apply hfinc k (max n k + 1)
              rw [@Nat.lt_succ] ; exact Nat.le_max_right n k
        }
        rw [← this] ; exact hC₂
      }
      specialize hCsub θ (f n) hn
      exact hCsub hCb
    · have : f 0 ≤ b := by
        apply le_csSup (Ordinal.bddAbove_range f) ; use 0
      exact LT.lt.trans_le hf₁ this
  }

theorem diag_int_club_unbounded (κ : Cardinal) (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (C : Ordinal → Set Ordinal) (hC : ∀ o : Ordinal, o < κ.ord → club_in (C o) κ.ord) :
    unbounded_in (diag_int κ.ord C) κ.ord := by
  {
    rw [diag_int_of_int]
    have hκ : Cardinal.aleph0 < κ.ord.cof := by
      rw [Cardinal.IsRegular.cof_eq hκ₁] ; exact hκ₂
    apply diag_int_club_sub_unbounded hκ
    intro o ho
    apply int_lt_card_club o hκ₁ hκ₂ (Cardinal.lt_ord.mp ho)
    · intro i hi
      exact hC i hi
    · intro a o hao
      intro x hx
      rw [@Set.mem_iInter] at *
      intro i
      have : i ≤ o := by
        obtain hi₂ := i.2 ; rw [@Set.mem_Iic] at hi₂
        apply le_of_lt ; exact LE.le.trans_lt hi₂ hao
      simp_all only [Subtype.forall, Set.mem_Iic]
  }

theorem diag_int_club {κ : Cardinal} (hκ₁ : κ.IsRegular) (hκ₂ : Cardinal.aleph0 < κ)
  (C : Ordinal → Set Ordinal) (hC : ∀ o : Ordinal, o < κ.ord → club_in (C o) κ.ord) :
  club_in (diag_int κ.ord C) κ.ord := by
{
  obtain hu := diag_int_club_unbounded κ hκ₁ hκ₂ C hC
  constructor
  · exact hu
  · intro b hb₁ hb₂
    set α := sSup (strict_Ordinal_res (diag_int κ.ord C) b)
    by_contra h'
    have hαb : α ≤ b := by
      apply csSup_le hb₂
      intro c hc ; exact le_of_lt hc.2
    have hακ : α < κ.ord := by
      exact lt_of_le_of_lt hαb hb₁
    have : sSup (strict_Ordinal_res (diag_int κ.ord C) b) ∉ strict_Ordinal_res (diag_int κ.ord C) b := by
      {
        by_contra h''
        have : α ∈ diag_int κ.ord C := by exact Set.mem_of_mem_inter_left h''
        exact h' this
      }
    have hα : sSup (strict_Ordinal_res (diag_int κ.ord C) α) = α := by
      exact (strict_csSup_res_csSup_res this hb₂).symm
    have hα₂ : Set.Nonempty (strict_Ordinal_res (diag_int κ.ord C) α) := by
      rw [(strict_res_csSup_res this hb₂).symm]
      exact hb₂
    have : ∃ θ : Ordinal, θ < α ∧ α ∉ C θ := by
    {
      by_contra h'₂ ; push_neg at h'₂
      have : α ∈ (diag_int κ.ord C) := by constructor ; exact hακ ; exact h'₂
      exact h' this
    }
    obtain ⟨ θ₀, hθ₀₁, hθ₀₂ ⟩ := this
    by_cases Set.Nonempty (strict_Ordinal_res (C θ₀) α)
    · have hαθ₀ : sSup (strict_Ordinal_res (C θ₀) α) ∈ C θ₀ := by
      {
        specialize hC θ₀ ; unfold club_in at hC
        have : θ₀ < Cardinal.ord κ := by
          exact gt_trans hακ hθ₀₁
        obtain ⟨ _, hC₂ ⟩ := hC this
        exact hC₂ α hακ h
      }
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
        v ∈ (diag_int κ.ord C) ∧ θ₀ < v ∧ v < α ∧ sSup (strict_Ordinal_res (C θ₀) α) < v := by
        {
          have h₄ : Set.Nonempty {x ∈ (strict_Ordinal_res (diag_int κ.ord C) α) |
            (max (sSup (strict_Ordinal_res (C θ₀) α)) θ₀) < x} := by
          {
            refine nonempty_lbd_of_sup (strict_Ordinal_res (diag_int κ.ord C) α)
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
    · have hv : ∃ v : Ordinal, v ∈ (diag_int κ.ord C) ∧ θ₀ < v ∧ v < α := by
        {
          have h₄ : Set.Nonempty {x ∈ (strict_Ordinal_res (diag_int κ.ord C) α) | θ₀ < x} := by
            refine nonempty_lbd_of_sup (strict_Ordinal_res (diag_int κ.ord C) α) θ₀ hα₂ ?_
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
    let C := diag_int κ.ord C'
    have hC : ( sub_Ordinal C κ.ord ) ∧ ( club_in C κ.ord ) := by
      {
        constructor
        · apply (sub_Ordinal_iff_strict_res_eq C (Cardinal.ord κ)).2
          intro c hc
          simp at hc ; rw [diag_int] at hc ; simp at hc ;  exact hc.1
        · refine diag_int_club hκ₁ hκ₂ C' ?hC'
          intro o _
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
