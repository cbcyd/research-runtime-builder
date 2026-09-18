import MemoryOperational.SoftmaxPhysicalSummary
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Operator.Banach

open Matrix BigOperators Filter Topology

namespace KernelOperational
namespace SoftmaxReachable

/-- The physical rich-cache summary map is strictly Fréchet differentiable at
the Vandermonde witness, with the same derivative already identified in the
ordinary Fréchet theorem. -/
theorem richSummaryMap_hasStrictFDerivAt
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    HasStrictFDerivAt (richSummaryMap (ν := ν) c lambda)
      (summaryJacobianCLM (ν := ν) c lambda) (richSummaryBase m ν) := by
  rw [← richSummaryDerivative_eq_summaryJacobian]
  unfold richSummaryMap richSummaryDerivative
  apply HasStrictFDerivAt.prodMk
  · rw [hasStrictFDerivAt_pi]
    intro j
    have hsum :
        HasStrictFDerivAt
          (fun x : SummaryTangent m ν =>
            ∑ t : Fin m, Real.exp (lambda j * x.1 t))
          (∑ t : Fin m,
            Real.exp (lambda j * (t : ℕ)) •
              (lambda j • tauProj (ν := ν) t))
          (richSummaryBase m ν) := by
      apply HasStrictFDerivAt.fun_sum
      intro t ht
      have hlin :
          HasStrictFDerivAt
            (fun x : SummaryTangent m ν => lambda j * x.1 t)
            (lambda j • tauProj (ν := ν) t)
            (richSummaryBase m ν) := by
        have hraw :
            HasStrictFDerivAt
              (fun x : SummaryTangent m ν =>
                (lambda j • tauProj (ν := ν) t) x)
              (lambda j • tauProj (ν := ν) t)
              (richSummaryBase m ν) :=
          (lambda j • tauProj (ν := ν) t).hasStrictFDerivAt
        simpa [tauProj, smul_eq_mul] using hraw
      simpa [richSummaryBase] using hlin.exp
    simpa using hsum.const_mul (c j)
  · rw [hasStrictFDerivAt_pi]
    intro a
    rw [hasStrictFDerivAt_pi]
    intro j
    have hsum :
        HasStrictFDerivAt
          (fun x : SummaryTangent m ν =>
            ∑ t : Fin m,
              Real.exp (lambda j * x.1 t) * x.2 a t)
          (∑ t : Fin m,
            Real.exp (lambda j * (t : ℕ)) • valueProj a t)
          (richSummaryBase m ν) := by
      apply HasStrictFDerivAt.fun_sum
      intro t ht
      have hlin :
          HasStrictFDerivAt
            (fun x : SummaryTangent m ν => lambda j * x.1 t)
            (lambda j • tauProj (ν := ν) t)
            (richSummaryBase m ν) := by
        have hraw :
            HasStrictFDerivAt
              (fun x : SummaryTangent m ν =>
                (lambda j • tauProj (ν := ν) t) x)
              (lambda j • tauProj (ν := ν) t)
              (richSummaryBase m ν) :=
          (lambda j • tauProj (ν := ν) t).hasStrictFDerivAt
        simpa [tauProj, smul_eq_mul] using hraw
      have hexp := hlin.exp
      have hval :
          HasStrictFDerivAt
            (fun x : SummaryTangent m ν => x.2 a t)
            (valueProj a t)
            (richSummaryBase m ν) := by
        have hraw :
            HasStrictFDerivAt
              (fun x : SummaryTangent m ν => valueProj a t x)
              (valueProj a t)
              (richSummaryBase m ν) :=
          (valueProj (m := m) a t).hasStrictFDerivAt
        simpa [valueProj] using hraw
      have hprod := hexp.mul hval
      change HasStrictFDerivAt
        ((fun x : SummaryTangent m ν =>
            Real.exp (lambda j * x.1 t)) *
          (fun x : SummaryTangent m ν => x.2 a t))
        (Real.exp (lambda j * (t : ℕ)) • valueProj a t)
        (richSummaryBase m ν)
      simpa [richSummaryBase] using hprod
    simpa using hsum.const_mul (c j)

/-- The continuous Jacobian is injective under the same Vandermonde hypotheses
as the previously checked algebraic Jacobian. -/
theorem summaryJacobianCLM_injective
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    Function.Injective (summaryJacobianCLM (ν := ν) c lambda) := by
  intro x y hxy
  apply summaryJacobian_injective c lambda hc hlambda0 hlambdaInj
  exact hxy

/-- Since the Jacobian is an endomorphism of one finite-dimensional space,
injectivity implies surjectivity. -/
theorem summaryJacobianCLM_surjective
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    Function.Surjective (summaryJacobianCLM (ν := ν) c lambda) := by
  exact LinearMap.injective_iff_surjective.mp
    (summaryJacobianCLM_injective c lambda hc hlambda0 hlambdaInj)

/-- Package the nonsingular physical-summary Jacobian as a continuous linear
equivalence, the derivative object expected by the inverse function theorem. -/
noncomputable def summaryJacobianEquiv
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    SummaryTangent m ν ≃L[ℝ] SummaryTangent m ν :=
  ContinuousLinearEquiv.ofBijective
    (summaryJacobianCLM (ν := ν) c lambda)
    (LinearMap.ker_eq_bot.mpr
      (summaryJacobianCLM_injective c lambda hc hlambda0 hlambdaInj))
    (LinearMap.range_eq_top.mpr
      (summaryJacobianCLM_surjective c lambda hc hlambda0 hlambdaInj))

/-- The strict derivative can be viewed through the continuous linear
equivalence used by inverse-function machinery. -/
theorem richSummaryMap_hasStrictFDerivAt_equiv
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    HasStrictFDerivAt (richSummaryMap (ν := ν) c lambda)
      ((summaryJacobianEquiv c lambda hc hlambda0 hlambdaInj :
        SummaryTangent m ν ≃L[ℝ] SummaryTangent m ν) :
        SummaryTangent m ν →L[ℝ] SummaryTangent m ν)
      (richSummaryBase m ν) := by
  have hbase :=
    richSummaryMap_hasStrictFDerivAt (ν := ν) c lambda
  apply hbase.congr_fderiv
  change summaryJacobianCLM (ν := ν) c lambda =
    ((summaryJacobianEquiv c lambda hc hlambda0 hlambdaInj :
      SummaryTangent m ν ≃L[ℝ] SummaryTangent m ν) :
      SummaryTangent m ν →L[ℝ] SummaryTangent m ν)
  symm
  unfold summaryJacobianEquiv
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _

/-- Machine-checked local inverse/open-image statement: the physical rich-cache
summary map sends the neighborhood filter of the Vandermonde cache witness
onto the neighborhood filter of its summary. -/
theorem richSummaryMap_map_nhds_eq
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    Filter.map (richSummaryMap (ν := ν) c lambda)
        (𝓝 (richSummaryBase m ν))
      =
    𝓝 (richSummaryMap (ν := ν) c lambda (richSummaryBase m ν)) := by
  exact (richSummaryMap_hasStrictFDerivAt_equiv
    c lambda hc hlambda0 hlambdaInj).map_nhds_eq_of_equiv

end SoftmaxReachable
end KernelOperational
