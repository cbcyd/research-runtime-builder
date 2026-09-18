import MemoryOperational.RestrictedSoftmaxRank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions

open Matrix BigOperators

namespace KernelOperational
namespace SoftmaxReachable

/-- Exponential evaluation matrix on the integer item coordinates. Rows are
queries/exponents and columns are independently moving cache items. -/
noncomputable def expMomentMatrix {m : ℕ} (lambda : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun j t => Real.exp (lambda j * (t : ℕ))

/-- The exponential evaluation matrix is the transpose of the power matrix
with distinct positive bases `exp lambda_j`. -/
theorem expMomentMatrix_eq_powerEvaluation_transpose
    {m : ℕ} (lambda : Fin m → ℝ) :
    expMomentMatrix lambda =
      (powerEvaluationMatrix (fun j => Real.exp (lambda j))).transpose := by
  ext j t
  simp [expMomentMatrix, powerEvaluationMatrix]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Distinct exponents make the exponential evaluation matrix nonsingular. -/
theorem expMomentMatrix_det_ne_zero
    {m : ℕ} (lambda : Fin m → ℝ) (hinj : Function.Injective lambda) :
    (expMomentMatrix lambda).det ≠ 0 := by
  rw [expMomentMatrix_eq_powerEvaluation_transpose, Matrix.det_transpose]
  exact powerEvaluationMatrix_det_ne_zero _ (Real.exp_injective.comp hinj)

/-- Tangent coordinates for the rich m-item cache family used in the
continuous-minimality argument: one key-line coordinate per item and one value
coordinate per item/value row. -/
abbrev SummaryTangent (m : ℕ) (ν : Type*) :=
  (Fin m → ℝ) × (ν → Fin m → ℝ)

/-- Dimension of the cache-parameter/summary tangent space. -/
theorem summaryTangent_finrank
    {m : ℕ} {ν : Type*} [Fintype ν] :
    Module.finrank ℝ (SummaryTangent m ν) = m * (1 + Fintype.card ν) := by
  unfold SummaryTangent
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp [Finset.sum_const, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Block-triangular Jacobian at zero historical values for the rich softmax
cache family. `c_j` is the positive base-key factor and `lambda_j` is the
query slope along the chosen key direction. -/
noncomputable def summaryJacobian
    {m : ℕ} {ν : Type*}
    (c lambda : Fin m → ℝ) : SummaryTangent m ν →ₗ[ℝ] SummaryTangent m ν where
  toFun x :=
    (fun j => c j * lambda j * (expMomentMatrix lambda *ᵥ x.1) j,
     fun a j => c j * (expMomentMatrix lambda *ᵥ x.2 a) j)
  map_add' := by
    intro x y
    apply Prod.ext
    · funext j
      change c j * lambda j * (expMomentMatrix lambda *ᵥ (x.1 + y.1)) j =
        c j * lambda j * (expMomentMatrix lambda *ᵥ x.1) j +
          c j * lambda j * (expMomentMatrix lambda *ᵥ y.1) j
      rw [Matrix.mulVec_add]
      simp only [Pi.add_apply]
      ring
    · funext a j
      change c j * (expMomentMatrix lambda *ᵥ (x.2 a + y.2 a)) j =
        c j * (expMomentMatrix lambda *ᵥ x.2 a) j +
          c j * (expMomentMatrix lambda *ᵥ y.2 a) j
      rw [Matrix.mulVec_add]
      simp only [Pi.add_apply]
      ring
  map_smul' := by
    intro r x
    apply Prod.ext
    · funext j
      change c j * lambda j * (expMomentMatrix lambda *ᵥ (r • x.1)) j =
        r * (c j * lambda j * (expMomentMatrix lambda *ᵥ x.1) j)
      rw [Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · funext a j
      change c j * (expMomentMatrix lambda *ᵥ (r • x.2 a)) j =
        r * (c j * (expMomentMatrix lambda *ᵥ x.2 a) j)
      rw [Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

/-- The block-triangular softmax summary Jacobian is injective whenever the
query slopes are distinct/nonzero and all base-key exponential factors are
nonzero. -/
theorem summaryJacobian_injective
    {m : ℕ} {ν : Type*}
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    Function.Injective (summaryJacobian (ν := ν) c lambda) := by
  intro x y hxy
  have hdet : (expMomentMatrix lambda).det ≠ 0 :=
    expMomentMatrix_det_ne_zero lambda hlambdaInj
  have hmass : expMomentMatrix lambda *ᵥ (x.1 - y.1) = 0 := by
    funext j
    have hj := congrArg (fun z : SummaryTangent m ν => z.1 j) hxy
    change c j * lambda j * (expMomentMatrix lambda *ᵥ x.1) j =
      c j * lambda j * (expMomentMatrix lambda *ᵥ y.1) j at hj
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    have hcoef : c j * lambda j ≠ 0 := mul_ne_zero (hc j) (hlambda0 j)
    exact sub_eq_zero.mpr (mul_left_cancel₀ hcoef (by simpa [mul_assoc] using hj))
  have hxy1sub : x.1 - y.1 = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmass
  have hxy1 : x.1 = y.1 := sub_eq_zero.mp hxy1sub
  have hxy2 : x.2 = y.2 := by
    funext a
    have hval : expMomentMatrix lambda *ᵥ (x.2 a - y.2 a) = 0 := by
      funext j
      have hj := congrArg (fun z : SummaryTangent m ν => z.2 a j) hxy
      change c j * (expMomentMatrix lambda *ᵥ x.2 a) j =
        c j * (expMomentMatrix lambda *ᵥ y.2 a) j at hj
      rw [Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      exact sub_eq_zero.mpr (mul_left_cancel₀ (hc j) hj)
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hdet hval)
  exact Prod.ext hxy1 hxy2

/-- Hence the Jacobian has full finite rank `m(D_v+1)`. This is the exact
linear-algebra step needed before applying an inverse-function/open-image
theorem to obtain a reachable open summary neighborhood. -/
theorem summaryJacobian_finrank_range
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    Module.finrank ℝ (LinearMap.range (summaryJacobian (ν := ν) c lambda))
      = m * (1 + Fintype.card ν) := by
  have hinj := summaryJacobian_injective (ν := ν) c lambda hc hlambda0 hlambdaInj
  rw [LinearMap.finrank_range_of_inj hinj]
  exact summaryTangent_finrank

end SoftmaxReachable
end KernelOperational
