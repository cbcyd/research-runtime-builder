import MemoryOperational.SoftmaxPhysicalSummary
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace KernelOperational
namespace SoftmaxReachable

/-- Any injective linear encoding of the rich softmax summary coordinate space
into a d-dimensional real state must have d at least m(D_v+1). -/
theorem linear_state_dimension_lower_bound
    {m d : ℕ} {ν : Type*} [Fintype ν]
    (encode : SummaryTangent m ν →ₗ[ℝ] (Fin d → ℝ))
    (hinj : Function.Injective encode) :
    m * (1 + Fintype.card ν) ≤ d := by
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [summaryTangent_finrank, Module.finrank_fin_fun] at hdim
  exact hdim

/-- The same lower bound holds for affine encodings: translation cannot hide
a linear dimension deficit. -/
theorem affine_state_dimension_lower_bound
    {m d : ℕ} {ν : Type*} [Fintype ν]
    (linearPart : SummaryTangent m ν →ₗ[ℝ] (Fin d → ℝ))
    (offset : Fin d → ℝ)
    (hinj : Function.Injective (fun x => linearPart x + offset)) :
    m * (1 + Fintype.card ν) ≤ d := by
  have hlinj : Function.Injective linearPart := by
    intro x y hxy
    apply hinj
    change linearPart x + offset = linearPart y + offset
    rw [hxy]
  exact linear_state_dimension_lower_bound linearPart hlinj

/-- An affine exact realization that separates all rich-summary states therefore
cannot use fewer than m(D_v+1) real coordinates. This is the machine-checkable
linear/affine minimality result, independent of the stronger continuous-state
topological obstruction. -/
theorem affine_exact_summary_realization_lower_bound
    {m d : ℕ} {ν : Type*} [Fintype ν]
    (linearPart : SummaryTangent m ν →ₗ[ℝ] (Fin d → ℝ))
    (offset : Fin d → ℝ)
    (hseparating :
      ∀ x y : SummaryTangent m ν,
        linearPart x + offset = linearPart y + offset → x = y) :
    m * (1 + Fintype.card ν) ≤ d := by
  apply affine_state_dimension_lower_bound linearPart offset
  intro x y hxy
  exact hseparating x y hxy

end SoftmaxReachable
end KernelOperational
