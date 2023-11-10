import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by
    {
      induction n
      case zero => rfl
      case succ k ih =>
        rw [sum_range_succ, ih]
        push_cast
        have h' : (∑ i in range (k + 1 + 1), ↑i) ^ 2 = ((∑ i in range (k + 1), ↑i ) + ( k + 1 ) ) ^ 2 := by
          {
            rw [sum_range_succ]
          }
        sorry
    }

open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [lin : LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min
  {
    unfold Pairwise
    unfold Disjoint
    simp
    have hsub : ∀ k, C k ⊆ A k := by
        {
          intro k
          specialize hC k
          intro x
          rw [hC]
          rw [Set.mem_diff]
          intro hx
          obtain ⟨ hx1, hx2 ⟩ := hx
          exact hx1
        }
    constructor
    · intro i j hij Y hY hY'
      have hY2 : Y ⊆ C i ∩ C j := by exact subset_inter hY hY'
      by_cases hij1 : j < i
      · have hCi : C i = A i \ ⋃ (j : ι) (_ : j < i), A j := by specialize hC i ; exact hC
        have hCj : C j = A j \ ⋃ (k : ι) (_ : k < j), A k := by specialize hC j ; exact hC
        have hCij : C i ∩ C j = ∅ := by
        {
          rw [hC, hC]
          ext u
          constructor
          · sorry
          · exfalso
        }
        exact subset_of_subset_of_eq hY2 hCij
      · simp at hij1
        have hij2 : i < j := by exact Ne.lt_of_le hij hij1
        have hCij : C i ∩ C j = ∅ := by sorry
        exact subset_of_subset_of_eq hY2 hCij
    · ext v
      constructor
      · intro hv
        simp
        simp at hv
        obtain ⟨ i₀, hi₀ ⟩ := hv
        specialize hsub i₀
        use i₀
        exact hsub hi₀
      · intro hv'
        simp
        simp at hv'
        have hmin : ∃ i, v ∈ A i ∧ ∀ j, v ∈ A j → j ≥ i := by
        {
          sorry
        }
        obtain ⟨ i₁, hi₁, hi₁' ⟩ := hmin
        use i₁
        rw [hC]
        rw [Set.mem_diff]
        constructor
        exact hi₁
        by_contra h'
        simp at h'
        obtain ⟨ j₁, hj₁, hj₁' ⟩ := h'
        specialize hi₁' j₁ hj₁'
        have h'' : i₁ < i₁ := by exact lt_of_le_of_lt hi₁' hj₁
        exact LT.lt.false h''
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h

  lemma onepos : (0 : ℝ) < (1 :ℝ ):= by norm_num


lemma exercise4_3 : Group PosReal where
   mul := fun a b ↦ ⟨ a.1 * b.1, mul_pos a.2 b.2 ⟩
   mul_assoc := by intro a b c ; apply PosReal.ext ; exact mul_assoc a.1 b.1 c.1
   one := ⟨ (1 : ℝ), onepos ⟩
   one_mul := by intro a ; apply PosReal.ext ; exact one_mul a.1
   mul_one := by intro a ; apply PosReal.ext ; exact mul_one a.1
   inv := fun a ↦ ⟨ a.1⁻¹ , inv_pos.2 a.2 ⟩
   mul_left_inv := by {
                   intro a ; apply PosReal.ext
                   have h : a.1 ≠ 0 := by by_contra eq ; (have g : a.1 > 0 := by exact a.2) ; linarith
                   apply inv_mul_cancel h
                  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma ne_zero_ne_one (n : ℕ) (h0 : n ≠ 0) (h1 : n ≠ 1) : 2 ≤ n := by
{
  induction n
  · case zero => exfalso ; exact h0 rfl
  · case succ k ih =>
      have h0' : k ≠ 0 := by exact Nat.succ_ne_succ.mp h1
      by_cases hk : k = 1
      · have : 2 = k + 1 := by exact Nat.succ_inj'.mpr (id hk.symm)
        exact Nat.le_of_eq this
      · push_neg at hk
        specialize ih h0' hk
        exact Nat.le_step ih
}

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
    {
      rw [prime_def_lt]
      constructor
      · intro hn
        by_cases h0 : n = 0
        · exact Or.inl h0
        · by_cases h1 : n = 1
          · right ; exact Or.inl h1
          · push_neg at h0 h1
            right
            right
            push_neg at hn
            have h2 : 2 ≤ n := by exact ne_zero_ne_one n h0 h1
            specialize hn h2
            obtain ⟨m, hm1, hm2, hm3⟩ := hn
            use m, (n / m)
            constructor
            · have hm0 : m ≠ 0 := by exact ne_zero_of_dvd_ne_zero h0 hm2
              exact ne_zero_ne_one m hm0 hm3
            · constructor
              · have hnm0 : n / m ≠ 0 := by
                  {
                    by_contra h'
                    by_cases hm0 : m = 0
                    · sorry
                    · rw [Nat.div_eq_zero_iff] at h'
                      linarith
                      exact Nat.pos_of_ne_zero hm0
                  }
                have hnm1 : n / m ≠ 1 := by
                  {
                    by_contra h'
                    have : n = m := by exact (eq_of_dvd_of_div_eq_one hm2 h').symm
                    linarith
                  }
                exact ne_zero_ne_one (n / m) hnm0 hnm1
              · exact Nat.eq_mul_of_div_eq_right hm2 rfl
      · intro hn'
        push_neg
        obtain h1|h2|h3 := hn'
        · intro hf ; exfalso ; linarith
        · intro hf ; exfalso ; linarith
        · intro hl
          obtain ⟨ a, b, ha, hb, hab⟩ := h3
          use a
          constructor
          · have hb' : 0 < b := by linarith
            have ha' : a = (n / b) := by exact (Nat.div_eq_of_eq_mul_left hb' hab).symm
            calc a
               = n / b := by exact ha'
              _≤ n / 2  := by sorry
              _< n := by exact log2_terminates n hl
          · constructor
            · exact Dvd.intro b (id hab.symm)
            · linarith
    }


lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
  · simp at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul 2 a b]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by
              { simp ; rw [Int.modEq_zero_iff_dvd] ; exact sub_one_dvd_pow_sub_one ((2 : ℤ) ^ a) b}
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by rw [one_pow] ; rw [sub_self]
  have h2 : 2 ^ 2 ≤ 2 ^ a := by apply pow_le_pow ; linarith ; exact ha
  have h3 : 1 ≤ 2 ^ a := by exact Nat.one_le_two_pow a
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    have : a < a * b := by apply lt_mul_right ; linarith ; linarith
    apply pow_lt_pow ; norm_num ; exact this
  rw [Nat.prime_def_lt] at hn
  obtain ⟨ hn1, hn2 ⟩ := hn
  have h' : 1 ≤ 2 ^ (a * b) := by exact Nat.one_le_two_pow (a * b)
  norm_cast at h
  specialize hn2 ( 2 ^ a - 1 ) h5 h
  exact h4 hn2



/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
    {
      unfold IsSquare
      by_contra h
      push_neg at h
      obtain ⟨ ⟨ r1, h1 ⟩ , ⟨ r2, h2 ⟩ ⟩ := h
      rw [← Nat.pow_two] at h1 h2
      have h1' : b = (r1 - a)*(r1 + a) := by
      {
         calc b
           = r1 ^ 2 - a ^ 2 := by exact (tsub_eq_of_eq_add_rev (id h1.symm)).symm
          _= (r1 - a)*(r1 + a) := by sorry
      }
      have h2' : a = (r2 - b)*(r2 + b) := by sorry
      have hba : b > a := by
      {
        have hr1 : (r1 : ℤ) - a ≥ 1 := by sorry
        have hr1' : r1 + a > a := by
        {
          have : ( r1 : ℤ ) ≥ 1 := by
          {
            calc ( r1 : ℤ )
               = (r1 - a) + a := by exact eq_add_of_sub_eq rfl
              _≥ 1 + a := by apply add_le_add ; exact hr1 ; rfl
              _≥ 1 := by exact Int.le.intro a rfl
          }
          sorry
        }
        sorry
      }
      have hab : a > b := by sorry
      linarith
    }
