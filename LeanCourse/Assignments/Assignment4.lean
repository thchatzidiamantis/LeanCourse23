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



lemma exercise4_3 : Group PosReal := by sorry

  lemma onepos : (0 : ℝ) < (1 :ℝ ):= by norm_num

  instance : Group PosReal where
   mul := fun a b ↦ ⟨ a.1 * b.1, mul_pos a.2 b.2 ⟩
   mul_assoc := by intro a b c ; apply PosReal.ext ; exact mul_assoc a.1 b.1 c.1
   one := ⟨ (1 : ℝ), onepos ⟩
   one_mul := by intro a ; apply PosReal.ext ; exact one_mul a.1
   mul_one := by intro a ; apply PosReal.ext ; exact mul_one a.1
   inv := fun a ↦ ⟨ a.1⁻¹ , inv_pos.2 a.2 ⟩
   mul_left_inv := by {
                   intro a ; apply PosReal.ext
                   have h : a.1 ≠ 0 := by sorry
                   apply inv_mul_cancel h
                  }


/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
    {
      constructor
      · intro hn
        simp
        rw [Not] at hn
        by_contra h'
        push_neg at h'
        have hpn : Nat.Prime n := by
          obtain ⟨ h1, h2, h3 ⟩ := h'
          sorry
        sorry
      sorry
    }


lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · sorry
  · sorry
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
  have h2 : 2 ^ 2 ≤ 2 ^ a := by sorry
  have h3 : 1 ≤ 2 ^ a := by sorry
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    sorry
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by sorry
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  sorry


/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
    {
      unfold IsSquare
      by_contra h
      push_neg at h
      obtain ⟨ ⟨ r1, h1 ⟩ , ⟨ r2, h2 ⟩ ⟩ := h
      have h11 : a ^ 2 + b = r1 ^ 2 := by exact Nat.pow_two h1
      have h22 : b ^ 2 + a = r2 ^ 2 := by exact Nat.pow_two h2
      have h1' : b = (r1 - a)*(r1 + a) := by
      {
         calc b
           = r1 ^ 2 - a ^ 2 := by exact (tsub_eq_of_eq_add_rev (id h11.symm)).symm
          _= (r1 - a)*(r1 + a) := by sorry
      }
      have h2' : a = (r2 - b)*(r2 + b) := by sorry
      have hba : b > a := by
      {
        have hr1 : r1 - a ≥ 1 := by sorry
        have hr1' : r1 + a > a := by
        {
          have : r1 ≥ 1 := by
          {
            sorry
          }
        }
      }
      have hab : a > b := by sorry
      linarith
    }
