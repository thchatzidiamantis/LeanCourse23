import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by
{
  by_contra h
  have h' : (p ∧ ¬p) := by
  {
    constructor
    · by_contra h'
      rw [Not] at h h h'
      have h2 : p ∨ (p → False) := by right ; exact h'
      specialize h h2
      exact h
    · by_contra h'
      rw [Not] at h h
      have h3 : p ∨ (p → False) := by left ; exact h'
      specialize h h3
      exact h
  }
  obtain ⟨ h1', h2' ⟩ := h'
  specialize h2' h1'
  exact h2'
}






/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by
    {
      unfold SequentialLimit
      rw [SequentialLimit] at hs
      intro e he
      specialize hs e he
      obtain ⟨ M, hM ⟩ := hs
      specialize hr M
      obtain ⟨ N, hN ⟩ := hr
      use N
      intro n hn
      specialize hN n
      specialize hN hn
      specialize hM (r n)
      specialize hM hN
      exact hM
    }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by
    {
      rw [SequentialLimit]
      rw [SequentialLimit] at hs₁
      rw [SequentialLimit] at hs₃
      intro ε hε
      have hε' : (ε/2) > 0 := by
        {
          exact half_pos hε
        }
      specialize hs₁ ε hε
      obtain ⟨ N1, hN1 ⟩ := hs₁
      specialize hs₃ ε hε
      obtain ⟨ N3, hN3 ⟩ := hs₃
      --use max N1 N3
      let M := max N1 N3
      have hM1 : M ≥ N1 := by exact Nat.le_max_left N1 N3
      have hM3 : M ≥ N3 := by apply Nat.le_max_right N1 N3
      use M
      intro n hn
      have hn1 : n ≥ N1 := by exact Nat.le_trans hM1 hn
      have hn3 : n ≥ N3 := by exact Nat.le_trans hM3 hn
      specialize hN1 n hn1 ; specialize hN3 n hn3
      simp only [abs_sub_lt_iff]
      rw [abs_sub_lt_iff] at hN1 hN3
      obtain ⟨ hN1, hN1' ⟩ := hN1 ; obtain ⟨ hN3, hN3' ⟩ := hN3
      specialize hs₁s₂ n ; specialize hs₂s₃ n
      constructor
      · calc s₂ n - a
           ≤ s₃ n - a := by apply sub_le_sub ; exact hs₂s₃ ; rfl
          _< ε := by exact hN3
      · calc a - s₂ n
           ≤ a - s₁ n := by apply sub_le_sub ; rfl ; exact hs₁s₂
          _< ε := by exact hN1'
    }


/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by
{
  unfold SequentialLimit
  intro ε hε
  simp
  use ⌈1/ε⌉₊
  intro n hn
  have : ((n : ℝ) + 1)⁻¹  > 0 := by
  {
    apply inv_pos_of_pos
    exact cast_add_one_pos n
  }
  rw [abs_of_pos]
  have h' : (⌈1/ε⌉₊ : ℝ) + 1 ≤ (n : ℝ) + 1 := by apply add_le_add_right ; exact cast_le.mpr hn
  have hn' : (1/ε : ℝ) + 1 ≤ (n : ℝ) + 1 := by apply add_le_add_right ; exact ceil_le.mp hn
  have h1 : (1/ε : ℝ) + 1 > 0 := by apply add_pos ; ring ; apply inv_pos_of_pos ; exact hε ; exact Real.zero_lt_one
  calc ((n : ℝ) + 1)⁻¹
      ≤ ((1/ε : ℝ)+ 1)⁻¹ := by exact inv_le_inv_of_le h1 hn'
     _= ε/(ε + 1) := by field_simp ; constructor ; apply add_comm
     _< ε := by apply _root_.div_lt_self ; exact hε ; simp ; exact hε
  exact this
}


/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by
{
  rw [SequentialLimit]
  intro ε hε
  simp
  have h2 : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by exact use_me
  have h1 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by exact exercise3_4
  rw [SequentialLimit] at h1 h2
  specialize h1 ε hε ; specialize h2 ε hε
  obtain ⟨ N1, hN1 ⟩ := h1 ; obtain ⟨ N2, hN2 ⟩ := h2
  let M := max N1 N2
  have hM1 : M ≥ N1 := by exact Nat.le_max_left N1 N2
  have hM2 : M ≥ N2 := by apply Nat.le_max_right N1 N2
  use M
  intro n hn
  rw [abs_lt]
  have hn1 : n ≥ N1 := by exact Nat.le_trans hM1 hn
  have hn2 : n ≥ N2 := by exact Nat.le_trans hM2 hn
  specialize hN1 n hn1 ; specialize hN2 n hn2
  rw [abs_lt] at hN1 hN2
  simp only [sub_zero] at hN1 hN2
  obtain ⟨ hN1, hN1' ⟩ := hN1 ; obtain ⟨ hN2, hN2' ⟩ := hN2
  constructor
  have :  (-1) / (↑n + 1) ≤ sin ↑n / (↑n + 1) := by
    {
      apply div_le_div_of_le
      apply add_nonneg
      exact cast_nonneg n
      norm_num
      exact neg_one_le_sin ↑n
    }
  calc -ε
      < -1 / (↑n + 1) := by exact hN2
     _≤ sin ↑n / (↑n + 1) := by exact this
  have :  sin ↑n / (↑n + 1) ≤ 1 / (↑n + 1) := by
    {
      apply div_le_div_of_le
      apply add_nonneg
      exact cast_nonneg n
      norm_num
      exact sin_le_one ↑n
    }
  calc sin ↑n / (↑n + 1)
      ≤ 1 / (↑n + 1) := by exact this
     _< ε := by exact hN1'
}

/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by
    {
      rw [SequentialLimit] at h1
      rw [NondecreasingSequence] at h2
      intro n
      by_contra hf
      simp at hf
      specialize h1 (u n - l)
      have hf' : 0 < u n - l  := by apply sub_pos.2 ; exact hf
      specialize h1 hf'
      specialize h2 n
      obtain ⟨ N, hN ⟩ := h1
      let M := max n N
      have hM1 : n ≤ M := by exact Nat.le_max_left n N
      have hM2 : M ≥ N := by exact Nat.le_max_right n N
      specialize h2 M hM1
      specialize hN M hM2
      have hM3 : u M - l ≥ 0 := by
        calc u M - l
           ≥ u n - l := by apply sub_le_sub h2 ; rfl
          _≥ 0 := by exact le_of_lt hf'
      have h' : |u M - l| = u M - l := by apply abs_eq_self.2 ; exact hM3
      have h'' : u M - l = |u M - l| := by exact id h'.symm
      have : u M - l < u n - l := by
        calc u M - l
           = |u M - l| := by exact id h'.symm
          _< u n - l := by exact hN
      linarith
    }

/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
    {
      ext u
      constructor
      · intro hu
        simp at hu
        simp
        obtain ⟨ h1, hu1 ⟩ := hu
        obtain ⟨ x, hx ⟩ := h1
        obtain ⟨ hx1, hx2 ⟩ := hx
        use x
        constructor
        · constructor
          · exact hx1
          · rw [hx2]
            exact hu1
        · exact hx2
      · intro hu'
        simp at hu'
        simp
        obtain ⟨ y, hy ⟩ := hu'
        obtain ⟨ hy1, hy2, hy3 ⟩ := hy
        constructor
        · use y
          constructor
          · tauto
          · tauto
        · tauto
    }

lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by
    {
      ext u
      constructor
      · intro hu
        unfold preimage at hu
        simp at hu
        simp
        have h2 : (2 : ℝ) > 0 := by linarith
        by_cases h: 0 ≤ u
        · right
          calc 2
            = Real.sqrt (2 ^ 2) := by rw [sqrt_sq] ; norm_num
           _= Real.sqrt 4 := by norm_num
           _≤ Real.sqrt (u ^ 2) := by exact Real.sqrt_le_sqrt hu
           _= u := by apply Real.sqrt_sq ; exact h
        · left
          simp at h
          have : 2 ≤ -u := by
            calc 2
               = Real.sqrt (2 ^ 2) := by rw [sqrt_sq] ; norm_num
              _= Real.sqrt 4 := by norm_num
              _≤ Real.sqrt (u ^ 2) := by apply Real.sqrt_le_sqrt hu
              _= |u| := by exact sqrt_sq_eq_abs u
              _= -u := by exact abs_of_neg h
          linarith
      · simp
        intro hu
        obtain hu1|hu2 := hu
        nlinarith
        nlinarith
    }
/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦  (f '' s) ∪ g '' t
  let R : Set γ → Set α × Set β :=
    fun s ↦ (f⁻¹' s, g⁻¹' s)
  use L, R
  constructor
  · ext u v
    simp
    constructor
    · intro h3
      obtain h3|h3' := h3
      · obtain ⟨ x, hx ⟩ := h3
        obtain ⟨ hx, hx' ⟩ := hx
        calc v
           = f x := by symm ; exact hx'
          _∈ u := by exact hx
      · obtain ⟨ x, hx ⟩ := h3'
        obtain ⟨ hx, hx' ⟩ := hx
        calc v
           = g x := by symm ; exact hx'
          _∈ u := by exact hx
    · intro h4
      by_cases v ∈ range f
      · left
        rw [range] at h
        simp at h
        obtain ⟨ y, hy ⟩ := h
        use y
        constructor
        calc f y
           = v := by exact hy
          _∈ u := by exact h4
        exact hy
      · right
        have r1 : v ∈ (range f)ᶜ := by exact h
        have r2 : v ∈ range g := by
        {
          by_contra h'
          have r3 : v ∈ (range g)ᶜ := by exact h'
          have r4 : v ∈ (range f)ᶜ ∩ (range g)ᶜ := by exact mem_inter h h'
          have r5 : v ∈ (range f ∪ range g)ᶜ := by
            {
              by_contra d
              simp at d r4
              obtain ⟨ r4, r4' ⟩  := r4
              specialize d r4
              exact h' d
            }
          calc v
             ∈ (range f ∪ range g)ᶜ := by exact r5
            _= univᶜ := by exact congrArg compl h2
            _= ∅ := by exact (r5 (h2' v)).elim
        }
        simp at r2
        obtain ⟨ y, hy ⟩ := r2
        use y
        constructor
        exact mem_of_eq_of_mem hy h4
        exact hy
  ext u z
  simp
  constructor
  · intro h
    obtain h|h' := h
    · obtain ⟨ x, hx1, hx2 ⟩ := h
      specialize hf' x z
      have hxz : x = z := by exact hf hx2
      exact mem_of_eq_of_mem (hf (id hx2.symm)) hx1
    · exfalso
      obtain ⟨ x, hx1, hx2 ⟩ := h'
      exact h1' z x (id hx2.symm)
  · intro h
    left
    use z
  simp
  constructor
  · intro h
    obtain h|h' := h
    · exfalso
      obtain ⟨ x, hx1, hx2 ⟩ := h
      exact h1' x z hx2
    · obtain ⟨ x, hx1, hx2 ⟩ := h'
      have hxz : x = z := by exact hg hx2
      exact mem_of_eq_of_mem (hg (id hx2.symm)) hx1
  · intro h
    right
    use z
