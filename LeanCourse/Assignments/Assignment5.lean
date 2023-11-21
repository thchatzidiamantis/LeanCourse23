import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun := fun x ↦ f x.1 + g x.2
  map_add' := by
    {
      intro x y
      ring
      rw [@Prod.fst_add, @Prod.snd_add]
      simp
      rw [@add_add_add_comm]
    }
  map_smul' := by
    {
      intro r x
      ring
      rw [RingHom.id_apply]
      rw [@smul_add]
      rw [@Prod.smul_fst, @Prod.smul_snd]
      rw [@LinearMap.map_smul] ; rw [@LinearMap.map_smul]
    }

example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := rfl-- should be rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

lemma pow_has_inv (r : R) (hr : IsAUnit r) : ∀ n : ℕ, IsAUnit (r ^ n) := by
{
  intro n
  obtain ⟨ y, hy ⟩ := hr
  use y ^ n
  rw [pow_mul_pow_eq_one n hy]
}

lemma unit_prod (u v : R) (hu : IsAUnit u) (hv : IsAUnit v) : IsAUnit (u * v) := by
{
  unfold IsAUnit ; unfold IsAUnit at hu hv
  obtain ⟨ u', hu' ⟩ := hu
  obtain ⟨ v', hv' ⟩ := hv
  use v' * u'
  calc v' * u' * (u * v)
     = v' * (u' * u) * v := by ring
    _= v' * 1 * v := by exact congrFun (congrArg HMul.hMul (congrArg (HMul.hMul v') hu')) v
    _= v' * v := by ring
    _= 1 := by exact hv'
}


instance exercise5_2 : Group {x : R // IsAUnit x} where
  mul := fun x y ↦ ⟨ x.1 * y.1, unit_prod x.1 y.1 x.2 y.2 ⟩
  mul_assoc := by intro a b c ; ext ; apply mul_assoc
  one := ⟨ 1, by {unfold IsAUnit ; use 1 ; ring} ⟩
  one_mul := by intro a ; ext ; apply one_mul
  mul_one := by intro a ; ext ; apply mul_one
  npow := fun n x ↦ ⟨ x.1 ^ n, pow_has_inv x.1 x.2 n ⟩
  npow_zero := by intro x ; group ; rfl
  npow_succ := by intro n ; intro x ; group ; rfl
  inv := fun x ↦ ⟨ Exists.choose x.2, by use x ; rw [mul_comm] ; exact Exists.choose_spec x.2 ⟩
  div := fun x y ↦ ⟨ x.1 * (Exists.choose y.2) , by use y.1 * (Exists.choose x.2) ; rw [mul_comm] ; sorry ⟩
  div_eq_mul_inv := _
  zpow := _
  zpow_zero' := _
  zpow_succ' := _
  zpow_neg' := _
  mul_left_inv := _
-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by sorry

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    {
      intro i hi
      rw [Nat.choose_eq_factorial_div_factorial]
      use (p-1) ! / (i ! * (p - i)!)
      calc p ! / (i ! * (p - i)!)
         = (p * (p-1)!) / (i ! * (p - i)!) := by rw [mul_factorial_pred h3]
        _= p * (p-1) ! / (i ! * (p - i)!) := by ring
        _= p * ((p - 1)! / (i ! * (p - i)!)) := sorry
      simp at hi ; linarith
    }
  have h7 : ∀ i ∈ Ioo 0 p, (Nat.choose p i : K) = 0 := by
    {
      intro i hi
      specialize h5 i hi
      rw [CharP.cast_eq_zero_iff K p]
      exact h5
    }
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by
         {
           sorry
         }
    _ = 0 := by apply sum_eq_zero ; exact fun x_1 a ↦ mul_zero (x ^ x_1 * y ^ (p - x_1))
  rw [sum_range_succ']
  simp
  rw [h4]
  sorry

/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
  rw [← smul_eq_mul]
  specialize h r
