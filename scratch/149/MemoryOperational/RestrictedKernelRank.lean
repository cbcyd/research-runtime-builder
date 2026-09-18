import MemoryOperational.KernelRealization
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

open Matrix

namespace KernelOperational

/-- Evaluation matrix of a finite family of scalar key-functions at a matching
finite family of key points. Columns correspond to functions. -/
def evaluationMatrix {σ K : Type*}
    (f : σ → K → ℝ) (points : σ → K) : Matrix σ σ ℝ :=
  fun i j => f j (points i)

/-- Simultaneous evaluation at the declared point family is linear. -/
def evalPointsLinear {σ K : Type*}
    (points : σ → K) : (K → ℝ) →ₗ[ℝ] (σ → ℝ) where
  toFun := fun g i => g (points i)
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl

/-- A nonsingular finite evaluation matrix certifies linear independence of
the original function family on the whole key domain. -/
theorem linearIndependent_of_evaluation_det_ne_zero
    {σ K : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → K → ℝ) (points : σ → K)
    (hdet : (evaluationMatrix f points).det ≠ 0) :
    LinearIndependent ℝ f := by
  apply LinearIndependent.of_comp (evalPointsLinear points)
  have hcols : LinearIndependent ℝ (evaluationMatrix f points).col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have heq : (evalPointsLinear points : (K → ℝ) →ₗ[ℝ] (σ → ℝ)) ∘ f
      = (evaluationMatrix f points).col := by
    funext j i
    rfl
  rw [heq]
  exact hcols

/-- Under the same certificate, the restricted function span has the maximum
possible dimension, equal to the number of declared queries/functions. -/
theorem finrank_restricted_span_eq_card_of_evaluation_det_ne_zero
    {σ K : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → K → ℝ) (points : σ → K)
    (hdet : (evaluationMatrix f points).det ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = Fintype.card σ := by
  exact finrank_span_eq_card (linearIndependent_of_evaluation_det_ne_zero f points hdet)

/-- Scalar softmax kernel function indexed by a declared query. -/
noncomputable def softmaxKernelFunction
    {σ κ : Type*} [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ) : σ → (κ → ℝ) → ℝ :=
  fun op k => Real.exp (scale * ∑ j, Q op j * k j)

/-- Any finite query family has restricted softmax kernel rank at most its
cardinality, independent of whether its query functions are redundant. -/
theorem softmaxKernelSpan_finrank_le_card
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ) :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range (softmaxKernelFunction scale Q)))
      ≤ Fintype.card σ := by
  exact finrank_range_le_card (softmaxKernelFunction scale Q)

/-- A nonsingular finite key-evaluation certificate proves that a finite
softmax query family has exact restricted rank equal to the number of queries. -/
theorem softmaxKernelSpan_finrank_eq_card_of_evaluation_det_ne_zero
    {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ) (keys : σ → κ → ℝ)
    (hdet : (evaluationMatrix (softmaxKernelFunction scale Q) keys).det ≠ 0) :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range (softmaxKernelFunction scale Q)))
      = Fintype.card σ := by
  exact finrank_restricted_span_eq_card_of_evaluation_det_ne_zero
    (softmaxKernelFunction scale Q) keys hdet

end KernelOperational
