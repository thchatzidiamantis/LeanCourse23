import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/

lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  {
    constructor
    · intro h
      obtain ⟨ x₀, h2|h3 ⟩ := h
      left
      use x₀
      right
      use x₀
    · intro h'
      obtain ⟨ x₀, h4 ⟩|h5 := h'
      use x₀
      left
      exact h4
      obtain ⟨ x₀, h6 ⟩ := h5
      use x₀
      right
      exact h6
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  {
    rw [SurjectiveFunction]
    rw [SurjectiveFunction] at h
    intro y
    specialize h y
    obtain ⟨ x₀, h2 ⟩ := h
    use f x₀
    exact h2
  }

/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  {
    constructor
    · apply exercise2_2
    · rw [SurjectiveFunction]
      rw [SurjectiveFunction]
      rw [SurjectiveFunction] at hf
      intro hg
      intro y
      specialize hg y
      obtain ⟨ z, h2 ⟩ := hg
      specialize hf z
      obtain ⟨ x₀, h3 ⟩ := hf
      use x₀
      simp
      rw [h3]
      exact h2
  }

/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  {
    have h: ( SurjectiveFunction (fun x ↦ 2 * f (x) + 1)) := by
    {
      intro y
      specialize hf ((1/2)*(y-1))
      obtain ⟨ x₀, h' ⟩ := hf
      use x₀
      ring
      rw [h']
      ring
    }
    have h': ( SurjectiveFunction (fun x ↦ 3 * (x+4))) := by
    {
      intro y
      use ((1/3*y-4))
      ring
    }
    rw [SurjectiveFunction]
    rw [SurjectiveFunction] at h
    rw [SurjectiveFunction] at h'
    intro y
    specialize h y
    obtain ⟨ z, h2 ⟩ := h
    specialize h' z
    obtain ⟨ x₀, h3 ⟩ := h'
    use x₀
    rw [h3]
    exact h2
  }

end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  {
    unfold EventuallyGrowsFaster
    intro k'
    use k'
    intro n
    intro h
    ring
    rw [mul_comm]
    exact Nat.mul_le_mul_left (s n) h
  }

/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  {
    unfold EventuallyGrowsFaster
    intro k'
    rw [EventuallyGrowsFaster] at h₁
    specialize h₁ k'
    obtain ⟨k1, h11⟩ := h₁
    rw [EventuallyGrowsFaster] at h₂
    specialize h₂ k'
    obtain ⟨k2, h22⟩ := h₂
    use max k1 k2
    intro n
    intro h
    simp
    ring
    rw [useful_fact] at h
    obtain ⟨h3, h4 ⟩ := h
    apply Nat.add_le_add
    apply h11
    exact h3
    apply h22
    exact h4
  }


/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  {
    unfold EventuallyGrowsFaster
    use fun n ↦ Nat.factorial n
    constructor
    · intro k'
      use k'
      intro n
      intro h
      have h': (fun n => (n + 1)!) n = n! * (n+1) := by
      {
        ring
        calc (1+n)!
        _= (n+1)! := by rw [add_comm]
        _= (n+1)*(n!) := by exact rfl
        _= n * n ! + 1*n ! := by rw [add_mul]
        _= n * n ! + n ! := by ring
      }
      rw [mul_comm]
      rw [h']
      apply Nat.mul_le_mul_left
      linarith
    · intro n
      exact factorial_ne_zero n
  }


/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact?
  · have : 1 ≤ n := by exact?
    exact?

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by
  have h3s : ∀ n, 1 ≤ s n := by
    intro n
    exact one_le_iff_ne_zero.mpr (h2s n)
  intro k'
  rw [EventuallyGrowsFaster] at hs
  specialize hs k'
  obtain ⟨ N, hn ⟩ := hs
  use N+1
  intro n
  intro h'
  have h4 : ∀ n ≥ N, s (n+1) ≥ k' := by
    intro n'
    intro h5
    specialize h3s n'
    specialize hn n'
    specialize hn h5
    simp
    exact le_of_mul_le_of_one_le_left hn h3s
  have h6 : ∃ m ≥ N, m + 1 = n := by
    apply useful_fact2
    exact h'
  obtain ⟨ m, h7, h8 ⟩ := h6
  specialize h4 m h7
  apply?



end Growth