import LeanCourse.Common
open Set Function Real
noncomputable section
set_option linter.unusedVariables false
variable {ι L : Type*}



/- # Today: Sets (continued) and functions

We cover sections 4.1, 4.2 and 4.3 from Mathematics in Lean.
Assignment 3 is posted and due on November 3. -/

/-
Last time we discussed negation `¬` (not), classical logic, sequences and sets.
-/

/- ## Proving two sets are equal

You can prove that two sets are equal by applying `subset_antisymm` or using the `ext` tactic.
-/


variable {α β : Type*} (x : α) (s t : Set α)

/- We saw last time that we can prove that two sets are equal using `ext`. -/
example : s ∩ t = t ∩ s := by
{
  ext x
  simp only [mem_inter_iff, and_comm]
}

/- We can also use existing lemmas and `calc`. -/
example : (s ∪ tᶜ) ∩ t = s ∩ t := by
{
  calc (s ∪ tᶜ) ∩ t
      = (s ∩ t) ∪ (tᶜ ∩ t) := by rw [@inter_distrib_right]
    _ = (s ∩ t) ∪ ∅ := by rw [@compl_inter_self]
    _ = s ∩ t := by rw [@union_empty]
}





/-
# Set-builder notation
-/

/- We can write `{x : α | p x}` to write the set of all elements in `α` where `p` holds. -/
def Evens : Set ℕ := {n : ℕ | Even n}
def Odds : Set ℕ := {n | ¬ Even n}

example : Evens ∪ Odds = univ := by
{
  ext n
  simp
  by_cases hn : Even n
  simp [Evens, Odds, hn]
  simp [Odds, Evens, hn]
}





/- All set operators can be written using the set-builder notation. -/
example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : sᶜ = {x | x ∉ s} := by rfl
example : (∅ : Set α) = {x | False} := by rfl
example : (univ : Set α) = {x | True} := by rfl


/-
# Other operations on sets
-/

/- We can take power sets. -/
example (s : Set α) : 𝒫 s = {t | t ⊆ s} := by rfl -- \powerset

/- What is the type of `𝒫 s`? -/


example (s t : Set α) : 𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t := by
{
  ext u
  simp only [mem_powerset_iff, subset_inter_iff, mem_inter_iff]
}






/- We can take unions and intersections of families of sets in three different ways:
* Given a family of sets `C : ι → Set α`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements of `ι`.
-/
example (C : ι → Set α) : ⋃ i : ι, C i = {x : α | ∃ i : ι, x ∈ C i} := by ext; simp

example (C : ι → Set α) : ⋂ i : ι, C i = {x : α | ∀ i : ι, x ∈ C i} := by ext; simp

/-
* Given a family of sets `C : ι → Set α` and `s : Set ι`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements in `s`.
-/
example (s : Set ι) (C : ι → Set α) : ⋃ i ∈ s, C i = {x : α | ∃ i ∈ s, x ∈ C i} := by ext; simp

example (s : Set ι) (C : ι → Set α) : ⋂ i ∈ s, C i = {x : α | ∀ i ∈ s, x ∈ C i} := by ext; simp

/-
* Given a collection of sets `C : Set (Set α)`
  we can take the union and intersection of `c`
  for all `c ∈ C`
-/

example (𝓒 : Set (Set α)) : ⋃₀ 𝓒 = {x : α | ∃ s ∈ 𝓒, x ∈ s} := by rfl

example (𝓒 : Set (Set α)) : ⋂₀ 𝓒 = {x : α | ∀ s ∈ 𝓒, x ∈ s} := by rfl

example (𝓒 : Set (Set α)) : ⋃₀ 𝓒 = ⋃ c ∈ 𝓒, c := by ext; simp



example (C : ι → Set α) (s : Set α) : s ∩ (⋃ i, C i) = ⋃ i, (C i ∩ s) := by
{
  ext x
  simp
  rw [and_comm]
}


/- We can take images and preimages of sets.

`f ⁻¹' s` is the preimage of `s` under `f`.
`f '' s` is the image of `s` under `f`. -/

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl

example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl


example {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
{
  constructor
  · intro h x hx
    simp
    apply h
    exact mem_image_of_mem f hx
  · intro h y hy
    obtain ⟨ x, hx, hxy⟩ := hy
    rw [← hxy]
    specialize h hx
    exact h
}

/-
If you have a hypothesis `h : y = t` or `h : t = y`,
where `y` is a variable (and `t` anything),
then you can use `h` to substitute `y` by `t` everywhere, using the tactic `subst h` or `subst y`.
This can also be done by `obtain` and `intro` by naming the equality `rfl`.
-/


/- We have another name for `f '' univ`, namely `range f`. -/
example (f : α → β) : f '' univ = range f := image_univ










/- We can do pointwise operations on sets. -/

open Pointwise

example (s t : Set ℝ) : s + t = {x : ℝ | ∃ a b, a ∈ s ∧ b ∈ t ∧ a + b = x } := by rfl
example (s t : Set ℝ) : -s = {x : ℝ | -x ∈ s } := by rfl

example : ({1, 3, 5} : Set ℝ) + {0, 10} = {1, 3, 5, 11, 13, 15} := by
{
  ext x
  simp [mem_add]
  norm_num
  tauto
}









/- # Exercises for the break. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by
{
  simp
  intro y hy
  exact hy
}

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by
{
  intro y hy
  simp
  specialize h y
  obtain ⟨a, ha⟩ := h
  use a
  constructor
  simp only [ha]
  exact hy
  · exact ha
}

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
{
  intro y hy
  simp at hy
  simp
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨x1, hx1, hx1'⟩:= hy1
  obtain ⟨x2, hx2, hx2'⟩:= hy2
  rw [Injective] at h
  have g : f x1 = f x2 := by
  {
    calc f x1 =
         y := by apply hx1'
       _= f x2 := by exact id hx2'.symm
  }
  specialize h g
  use x1
  constructor
  · constructor
    · exact hx1
    · exact mem_of_eq_of_mem h hx2
  · exact hx1'
}

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
{
  ext x
  simp
  constructor
  · intro h1
    obtain ⟨ x1, hx1, hx1'⟩:= h1
    obtain ⟨ i₀, hi₀⟩ := hx1
    use i₀
    use x1
  · intro h1
    obtain ⟨ i₀, hi₀⟩ := h1
    obtain ⟨ x1, hx1, hx1'⟩:= hi₀
    use x1
    constructor
    use i₀
    exact hx1'
}

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by sorry


/-
## Inverse of a function.

Suppose we have a function `f : α → β`.
Can we find a inverse `g : β → α` of `f`? Not without assuming that `f` is bijective...
But suppose we try, suppose that `∃ x, f x = y`, and we want to define `g y`.
It must be one of the `x` such that `f x = y`.
We can choose one such `x` using *the axiom of choice*.
-/

section Inverse

variable (f : α → β)

#check Classical.choose
#check Classical.choose_spec
open Classical

def conditionalInverse (y : β) (h : ∃ x, f x = y) : α :=
   Classical.choose h

lemma invFun_spec (y : β) (h : ∃ x, f x = y) : f (conditionalInverse f y h) = y := sorry


/- We can now define the function by cases on whether it lies in the range of `f` or not. -/

variable [Inhabited α]
def inverse (f : α → β) (y : β) : α :=
    if h: ∃ x : α, f x = y then
    conditionalInverse f y h else
    default

local notation "g" => inverse f -- let's call this function `g`


/- We can now prove that `g` is a right-inverse if `f` is surjective
and a left-inverse if `f` is injective.
We use the `ext` tactic to show that two functions are equal. -/
example (hf : Surjective f) : f ∘ g = id := by
{
  ext y
  simp
  obtain ⟨ x, rfl ⟩ := hf y
  simp [inverse, invFun_spec]
}

example (hf : Injective f) : g ∘ f = id := by
{
  ext x
  simp [inverse]
  have : ∀ x y : α, f x = f y ↔ x = y
  · intro x y
    exact hf.eq_iff
  apply hf
  simp [invFun_spec]
}


end Inverse

/-
## Cantor's theorem

Let's prove Cantor's theorem: there is no surjective function from any set to its power set. -/

example : ¬ ∃ (α : Type*) (f : α → Set α), Surjective f := by
{
  sorry
}


/- In section 4.3 of MIL you can read the proof of the Cantor-Schröder-Bernstein theorem. -/

example {f : α → β} {g : β → α}
    (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  sorry -- see MIL
