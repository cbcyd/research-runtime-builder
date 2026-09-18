import MemoryOperational.SoftmaxPredictiveQuotient

namespace KernelOperational
namespace SoftmaxPositiveMass

open SoftmaxSeparation
open SoftmaxPredictiveQuotient
open KernelOperational.Realization

/-- Every nonempty ordinary-softmax raw cache has strictly positive
normalization mass at every declared query. -/
theorem rawDenom_pos_of_nonempty
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (op : σ)
    (items : List ((κ → ℝ) × (ν → ℝ)))
    (hne : items ≠ []) :
    0 < State.rawDenom (softmaxFiniteFactorization scale Q) op items := by
  cases items with
  | nil => exact (hne rfl).elim
  | cons item rest =>
      simp only [State.rawDenom, List.map_cons, List.sum_cons,
        softmaxFiniteFactorization]
      have hhead :
          0 < Real.exp (scale * ∑ j, Q op j * item.1 j) :=
        Real.exp_pos _
      have htail :
          0 ≤
            (rest.map
              (fun item =>
                Real.exp (scale * ∑ j, Q op j * item.1 j))).sum := by
        apply List.sum_nonneg
        intro x hx
        rcases List.mem_map.mp hx with ⟨item', _, rfl⟩
        exact (Real.exp_pos _).le
      exact add_pos_of_pos_of_nonneg hhead htail

/-- The compiled denominator inherits strict positivity from every nonempty
ordinary-softmax physical cache. -/
theorem compile_denom_pos_of_nonempty
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (op : σ)
    (items : List ((κ → ℝ) × (ν → ℝ)))
    (hne : items ≠ []) :
    0 < State.denom (softmaxFiniteFactorization scale Q)
      (State.compile (softmaxFiniteFactorization scale Q) items) op := by
  rw [State.compile_denom]
  exact rawDenom_pos_of_nonempty scale Q op items hne

/-- In the one-hot finite-query softmax factorization, the first coordinate
of querySummary is exactly the normalized-read denominator. -/
theorem querySummary_fst_eq_denom
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (x : State (softmaxFiniteFactorization scale Q) ν)
    (op : σ) :
    (querySummary scale Q x op).1 =
      State.denom (softmaxFiniteFactorization scale Q) x op := by
  classical
  simp [querySummary, State.denom, softmaxFiniteFactorization]

/-- Hence the positive-mass side condition used by the predictive quotient
theorem is automatic for every nonempty ordinary-softmax raw cache. -/
theorem querySummary_compile_mass_pos_of_nonempty
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (items : List ((κ → ℝ) × (ν → ℝ)))
    (hne : items ≠ []) :
    ∀ op, 0 < (querySummary scale Q
      (State.compile (softmaxFiniteFactorization scale Q) items) op).1 := by
  intro op
  rw [querySummary_fst_eq_denom]
  exact compile_denom_pos_of_nonempty scale Q op items hne

/-- Concrete predictive quotient theorem with no abstract positivity premise:
for nonempty ordinary-softmax caches, equality of finite-query compiled states
is exactly predictive equivalence under all common future KV append words. -/
theorem compile_eq_iff_all_append_futures_equivalent_nonempty
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [Nonempty ν]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (xs ys : List ((κ → ℝ) × (ν → ℝ)))
    (hxs : xs ≠ []) (hys : ys ≠ [])
    (kstar : κ → ℝ) :
    State.compile (softmaxFiniteFactorization scale Q) xs
        = State.compile (softmaxFiniteFactorization scale Q) ys
      ↔
    (rawMachine (ν := ν) (softmaxFiniteFactorization scale Q)).equivalent
      (fun _ => True) xs ys := by
  exact compile_eq_iff_all_append_futures_equivalent_positive_mass
    scale Q xs ys kstar
    (querySummary_compile_mass_pos_of_nonempty scale Q xs hxs)
    (querySummary_compile_mass_pos_of_nonempty scale Q ys hys)

end SoftmaxPositiveMass
end KernelOperational
