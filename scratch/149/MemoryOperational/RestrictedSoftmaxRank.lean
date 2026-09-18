import MemoryOperational.RestrictedKernelRank
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open Matrix BigOperators Filter

namespace KernelOperational

/-- Polynomial-root form of the square Vandermonde injectivity argument.
If a degree < n polynomial vanishes at n distinct real points, all of its
coefficients vanish. -/
theorem coeffPolynomial_eq_zero_of_evaluations
    {n : ℕ} (x c : Fin n → ℝ)
    (hx : Function.Injective x)
    (heval : ∀ j : Fin n, ∑ i : Fin n, c i * x j ^ (i : ℕ) = 0) :
    c = 0 := by
  by_cases hn : n = 0
  · subst n
    funext i
    exact Fin.elim0 i
  let p : Polynomial ℝ := ∑ i : Fin n, Polynomial.monomial (i : ℕ) (c i)
  have hpdeg : p.natDegree < n := by
    have hdeg : p.natDegree ≤ n - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro i hi
      split
      · rename_i hEq
        have hi_lt : (i : ℕ) < n := i.isLt
        omega
      · rfl
    omega
  have hpeval : ∀ j : Fin n, Polynomial.eval (x j) p = 0 := by
    intro j
    simpa [p, Polynomial.eval_finset_sum, Polynomial.eval_monomial] using heval j
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hx hpeval (by simpa using hpdeg)
  funext i
  have hci : p.coeff (i : ℕ) = c i := by
    simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      have hne : (b : ℕ) ≠ (i : ℕ) := by
        intro h
        exact hbi (Fin.ext h)
      simp [hne]
    · simp
  have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff (i : ℕ)) hpzero
  rw [hci] at hcoeff
  simpa using hcoeff

/-- Square power-evaluation matrix, a transpose-oriented Vandermonde matrix. -/
def powerEvaluationMatrix {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun m j => x j ^ (m : ℕ)

/-- Distinct bases make the power-evaluation matrix nonsingular. This is the
Vandermonde fact needed by the softmax proof, derived here from the polynomial
root bound already present in the offline bundle. -/
theorem powerEvaluationMatrix_det_ne_zero
    {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x) :
    (powerEvaluationMatrix x).det ≠ 0 := by
  intro hdet
  rcases (Matrix.exists_vecMul_eq_zero_iff.mpr hdet) with ⟨c, hcne, hcz⟩
  have heval : ∀ j : Fin n, ∑ i : Fin n, c i * x j ^ (i : ℕ) = 0 := by
    intro j
    have hj := congrFun hcz j
    simpa [Matrix.vecMul, dotProduct, powerEvaluationMatrix] using hj
  exact hcne (coeffPolynomial_eq_zero_of_evaluations x c hx heval)

/-- Integer-spaced keys along one chosen key-space direction. -/
def integerLineKeys
    {n : ℕ} {κ : Type*} [Fintype κ]
    (u : κ → ℝ) (m : Fin n) : κ → ℝ :=
  fun a => (m : ℕ) * u a

/-- Query exponents induced by a key-space direction. -/
def lineExponents
    {n : ℕ} {κ : Type*} [Fintype κ]
    (scale : ℝ) (Q : Fin n → κ → ℝ) (u : κ → ℝ) : Fin n → ℝ :=
  fun op => scale * ∑ a, Q op a * u a

/-- Sampling softmax on integer points of a key line gives exactly a square
power-evaluation matrix with bases exp(lambda_j). -/
theorem softmax_evaluation_integer_line_eq_powerMatrix
    {n : ℕ} {κ : Type*} [Fintype κ]
    (scale : ℝ) (Q : Fin n → κ → ℝ) (u : κ → ℝ) :
    evaluationMatrix (softmaxKernelFunction scale Q) (integerLineKeys u)
      = powerEvaluationMatrix (fun op => Real.exp (lineExponents scale Q u op)) := by
  ext m op
  simp only [evaluationMatrix, softmaxKernelFunction, integerLineKeys,
    lineExponents, powerEvaluationMatrix]
  rw [← Real.exp_nat_mul]
  congr 1
  have hsum :
      (∑ a, Q op a * ((m : ℕ) * u a))
        = (m : ℕ) * ∑ a, Q op a * u a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    norm_num
    ring
  rw [hsum]
  ring

/-- A separating key-space direction therefore gives an explicit nonsingular
finite softmax evaluation matrix. -/
theorem softmax_integer_line_evaluation_det_ne_zero
    {n : ℕ} {κ : Type*} [Fintype κ]
    (scale : ℝ) (Q : Fin n → κ → ℝ) (u : κ → ℝ)
    (hsep : Function.Injective (lineExponents scale Q u)) :
    (evaluationMatrix (softmaxKernelFunction scale Q) (integerLineKeys u)).det ≠ 0 := by
  rw [softmax_evaluation_integer_line_eq_powerMatrix]
  exact powerEvaluationMatrix_det_ne_zero _ (Real.exp_injective.comp hsep)

/-- Exact restricted softmax kernel rank: whenever one key direction separates
all declared query projections, the restricted feature rank is exactly the
number of queries. -/
theorem softmaxKernelSpan_finrank_eq_card_of_separating_direction
    {n : ℕ} {κ : Type*} [Fintype κ]
    (scale : ℝ) (Q : Fin n → κ → ℝ) (u : κ → ℝ)
    (hsep : Function.Injective (lineExponents scale Q u)) :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range (softmaxKernelFunction scale Q))) = n := by
  have h := softmaxKernelSpan_finrank_eq_card_of_evaluation_det_ne_zero
    scale Q (integerLineKeys u)
    (softmax_integer_line_evaluation_det_ne_zero scale Q u hsep)
  simpa using h

/-- Polynomial encoding of the coordinatewise difference between two queries. -/
noncomputable def queryDifferencePolynomial
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (i j : Fin n) : Polynomial ℝ :=
  ∑ a : Fin d, Polynomial.monomial (a : ℕ) (Q i a - Q j a)

@[simp] theorem queryDifferencePolynomial_coeff
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (i j : Fin n) (a : Fin d) :
    (queryDifferencePolynomial Q i j).coeff (a : ℕ) = Q i a - Q j a := by
  simp only [queryDifferencePolynomial, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : (b : ℕ) ≠ (a : ℕ) := by
      intro h
      exact hba (Fin.ext h)
    simp [hne]
  · simp

/-- Distinct query vectors give a nonzero coordinate polynomial. -/
theorem queryDifferencePolynomial_ne_zero
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (hQ : Function.Injective Q)
    {i j : Fin n} (hij : i ≠ j) :
    queryDifferencePolynomial Q i j ≠ 0 := by
  intro hp
  have hfun : Q i = Q j := by
    funext a
    have hc := congrArg (fun p : Polynomial ℝ => p.coeff (a : ℕ)) hp
    rw [queryDifferencePolynomial_coeff] at hc
    simpa using sub_eq_zero.mp hc
  exact hij (hQ hfun)

/-- Evaluating the difference polynomial is exactly projection on the power
curve direction `(1,t,t^2,...)`. -/
theorem eval_queryDifferencePolynomial
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (i j : Fin n) (t : ℝ) :
    Polynomial.eval t (queryDifferencePolynomial Q i j)
      = ∑ a : Fin d, (Q i a - Q j a) * t ^ (a : ℕ) := by
  simp only [queryDifferencePolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial]

/-- One-parameter family of key-space directions used to avoid all pairwise
query-collision hyperplanes at once. -/
def powerDirection {d : ℕ} (t : ℝ) : Fin d → ℝ :=
  fun a => t ^ (a : ℕ)

/-- For a finite injective query family, there is a scalar parameter for which
all pairwise query projections on the power-curve direction are distinct. -/
theorem exists_powerDirection_separates_queries
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (hQ : Function.Injective Q) :
    ∃ t : ℝ, Function.Injective (fun op => ∑ a, Q op a * powerDirection t a) := by
  have hevent : ∀ᶠ t : ℝ in Filter.cofinite,
      ∀ i j : Fin n, i ≠ j →
        Polynomial.eval t (queryDifferencePolynomial Q i j) ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i = j
    · subst j
      filter_upwards [] with t
      intro hne
      exact (hne rfl).elim
    · have hp := Polynomial.eventually_cofinite_not_isRoot
        (queryDifferencePolynomial_ne_zero Q hQ hij)
      filter_upwards [hp] with t ht
      intro _
      simpa [Polynomial.IsRoot] using ht
  rcases hevent.exists with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro i j hijproj
  by_contra hij
  have hne := ht i j hij
  rw [eval_queryDifferencePolynomial] at hne
  apply hne
  have hzero :
      (∑ a, Q i a * powerDirection t a) -
        (∑ a, Q j a * powerDirection t a) = 0 := sub_eq_zero.mpr hijproj
  rw [← Finset.sum_sub_distrib] at hzero
  simpa [powerDirection, sub_mul] using hzero

/-- Nonzero softmax scale preserves the separating projection property. -/
theorem exists_separating_direction_for_softmax
    {n d : ℕ} (scale : ℝ) (hscale : scale ≠ 0)
    (Q : Fin n → Fin d → ℝ) (hQ : Function.Injective Q) :
    ∃ u : Fin d → ℝ, Function.Injective (lineExponents scale Q u) := by
  rcases exists_powerDirection_separates_queries Q hQ with ⟨t, ht⟩
  refine ⟨powerDirection t, ?_⟩
  intro i j hij
  apply ht
  apply mul_left_cancel₀ hscale
  simpa [lineExponents] using hij

/-- Generic finite-query softmax rank on the full Euclidean key domain: distinct
queries and nonzero scale force exact restricted kernel rank `n`. -/
theorem softmaxKernelSpan_finrank_eq_card_of_injective_queries
    {n d : ℕ} (scale : ℝ) (hscale : scale ≠ 0)
    (Q : Fin n → Fin d → ℝ) (hQ : Function.Injective Q) :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range (softmaxKernelFunction scale Q))) = n := by
  rcases exists_separating_direction_for_softmax scale hscale Q hQ with ⟨u, hu⟩
  exact softmaxKernelSpan_finrank_eq_card_of_separating_direction scale Q u hu

end KernelOperational
