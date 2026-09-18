import MemoryOperational.SoftmaxReachableJacobian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod

open Matrix BigOperators

namespace KernelOperational
namespace SoftmaxReachable

/-- The Vandermonde witness point: integer key-line coordinates and zero
historical values. -/
def richSummaryBase (m : ℕ) (ν : Type*) [Fintype ν] : SummaryTangent m ν :=
  (fun t => (t : ℕ), fun _ _ => 0)

/-- The actual nonlinear cache-parameter to finite-query softmax summary map.
The first block is the per-query mass Z. The second block is the per-query
value moment M. The constants c_j absorb the fixed base-key factor and
lambda_j is the query slope along the chosen key direction. -/
noncomputable def richSummaryMap
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    SummaryTangent m ν → SummaryTangent m ν :=
  fun x =>
    (fun j => c j * ∑ t : Fin m, Real.exp (lambda j * x.1 t),
     fun a j => c j * ∑ t : Fin m,
       Real.exp (lambda j * x.1 t) * x.2 a t)

/-- Continuous projection onto one key-line coordinate. -/
def tauProj
    {m : ℕ} {ν : Type*} [Fintype ν] (t : Fin m) :
    SummaryTangent m ν →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj t).comp
    (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (ν → Fin m → ℝ))

/-- Continuous projection onto one value coordinate of one cache item. -/
def valueProj
    {m : ℕ} {ν : Type*} [Fintype ν] (a : ν) (t : Fin m) :
    SummaryTangent m ν →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj t).comp
    ((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (ν → Fin m → ℝ)))

/-- Derivative assembled directly from coordinatewise scalar calculus at the
Vandermonde witness. A later theorem identifies this operator exactly with the
previously defined block-form summaryJacobian. -/
noncomputable def richSummaryDerivative
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    SummaryTangent m ν →L[ℝ] SummaryTangent m ν :=
  (ContinuousLinearMap.pi fun j =>
      c j • ∑ t : Fin m,
        Real.exp (lambda j * (t : ℕ)) •
          (lambda j • tauProj (ν := ν) t)).prod
    (ContinuousLinearMap.pi fun a =>
      ContinuousLinearMap.pi fun j =>
        c j • ∑ t : Fin m,
          Real.exp (lambda j * (t : ℕ)) • valueProj a t)

/-- Continuous-linear promotion of the algebraic candidate Jacobian. The
domain is finite-dimensional, so every linear map is continuous. -/
noncomputable def summaryJacobianCLM
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    SummaryTangent m ν →L[ℝ] SummaryTangent m ν :=
  LinearMap.toContinuousLinearMap
    (summaryJacobian (ν := ν) c lambda)

/-- The nonlinear physical summary map has the explicitly assembled derivative
at the Vandermonde witness. -/
theorem richSummaryMap_hasFDerivAt
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    HasFDerivAt (richSummaryMap (ν := ν) c lambda)
      (richSummaryDerivative c lambda) (richSummaryBase m ν) := by
  unfold richSummaryMap richSummaryDerivative
  apply HasFDerivAt.prodMk
  · rw [hasFDerivAt_pi]
    intro j
    have hsum :
        HasFDerivAt
          (fun x : SummaryTangent m ν =>
            ∑ t : Fin m, Real.exp (lambda j * x.1 t))
          (∑ t : Fin m,
            Real.exp (lambda j * (t : ℕ)) •
              (lambda j • tauProj (ν := ν) t))
          (richSummaryBase m ν) := by
      apply HasFDerivAt.fun_sum
      intro t ht
      have hlin :
          HasFDerivAt
            (fun x : SummaryTangent m ν => lambda j * x.1 t)
            (lambda j • tauProj (ν := ν) t)
            (richSummaryBase m ν) := by
        have hraw :
            HasFDerivAt
              (fun x : SummaryTangent m ν =>
                (lambda j • tauProj (ν := ν) t) x)
              (lambda j • tauProj (ν := ν) t)
              (richSummaryBase m ν) :=
          (lambda j • tauProj (ν := ν) t).hasFDerivAt
        simpa [tauProj, smul_eq_mul] using hraw
      simpa [richSummaryBase] using hlin.exp
    simpa using hsum.const_mul (c j)
  · rw [hasFDerivAt_pi]
    intro a
    rw [hasFDerivAt_pi]
    intro j
    have hsum :
        HasFDerivAt
          (fun x : SummaryTangent m ν =>
            ∑ t : Fin m,
              Real.exp (lambda j * x.1 t) * x.2 a t)
          (∑ t : Fin m,
            Real.exp (lambda j * (t : ℕ)) • valueProj a t)
          (richSummaryBase m ν) := by
      apply HasFDerivAt.fun_sum
      intro t ht
      have hlin :
          HasFDerivAt
            (fun x : SummaryTangent m ν => lambda j * x.1 t)
            (lambda j • tauProj (ν := ν) t)
            (richSummaryBase m ν) := by
        have hraw :
            HasFDerivAt
              (fun x : SummaryTangent m ν =>
                (lambda j • tauProj (ν := ν) t) x)
              (lambda j • tauProj (ν := ν) t)
              (richSummaryBase m ν) :=
          (lambda j • tauProj (ν := ν) t).hasFDerivAt
        simpa [tauProj, smul_eq_mul] using hraw
      have hexp := hlin.exp
      have hval :
          HasFDerivAt
            (fun x : SummaryTangent m ν => x.2 a t)
            (valueProj a t)
            (richSummaryBase m ν) := by
        have hraw :
            HasFDerivAt
              (fun x : SummaryTangent m ν => valueProj a t x)
              (valueProj a t)
              (richSummaryBase m ν) :=
          (valueProj (m := m) a t).hasFDerivAt
        simpa [valueProj] using hraw
      have hprod := hexp.mul hval
      change HasFDerivAt
        ((fun x : SummaryTangent m ν =>
            Real.exp (lambda j * x.1 t)) *
          (fun x : SummaryTangent m ν => x.2 a t))
        (Real.exp (lambda j * (t : ℕ)) • valueProj a t)
        (richSummaryBase m ν)
      simpa [richSummaryBase] using hprod
    simpa using hsum.const_mul (c j)

/-- The coordinatewise calculus derivative is exactly the previously defined
block Jacobian. -/
theorem richSummaryDerivative_eq_summaryJacobian
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    richSummaryDerivative (ν := ν) c lambda =
      summaryJacobianCLM (ν := ν) c lambda := by
  apply ContinuousLinearMap.ext
  intro h
  apply Prod.ext
  · funext j
    simp [richSummaryDerivative, summaryJacobianCLM, tauProj, summaryJacobian,
      expMomentMatrix, Matrix.mulVec, dotProduct, smul_eq_mul]
    calc
      c j * ∑ t : Fin m,
          Real.exp (lambda j * (t : ℕ)) * (lambda j * h.1 t)
          =
        c j * (lambda j *
          ∑ t : Fin m, Real.exp (lambda j * (t : ℕ)) * h.1 t) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            ring
      _ = c j * lambda j *
          ∑ t : Fin m, Real.exp (lambda j * (t : ℕ)) * h.1 t := by
            ring
  · funext a j
    simp [richSummaryDerivative, summaryJacobianCLM, valueProj, summaryJacobian,
      expMomentMatrix, Matrix.mulVec, dotProduct, smul_eq_mul]

/-- This closes the formal bridge left open by the audit: the previously
machine-checked full-rank summaryJacobian is the actual Fréchet derivative of
the physical rich-cache summary map at the Vandermonde witness. -/
theorem richSummaryMap_hasFDerivAt_summaryJacobian
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    HasFDerivAt (richSummaryMap (ν := ν) c lambda)
      (summaryJacobianCLM (ν := ν) c lambda) (richSummaryBase m ν) := by
  rw [← richSummaryDerivative_eq_summaryJacobian]
  exact richSummaryMap_hasFDerivAt c lambda

end SoftmaxReachable
end KernelOperational
