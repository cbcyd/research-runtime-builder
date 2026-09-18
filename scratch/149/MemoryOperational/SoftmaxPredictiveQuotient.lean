import MemoryOperational.SoftmaxSeparation

namespace KernelOperational
namespace SoftmaxPredictiveQuotient

open MemoryOperational
open KernelOperational.Realization
open KernelOperational.SoftmaxSeparation

/-- On positive-mass raw caches, equality of the exact finite-query softmax
compiler state is equivalent to predictive equivalence under arbitrary common
future KV appends. The reverse direction is witnessed already by the one-step
subfamily consisting of one fixed future key with arbitrary future value. -/
theorem compile_eq_iff_all_append_futures_equivalent_positive_mass
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [Nonempty ν]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (xs ys : List ((κ → ℝ) × (ν → ℝ)))
    (kstar : κ → ℝ)
    (hx : ∀ op, 0 < (querySummary scale Q
      (State.compile (softmaxFiniteFactorization scale Q) xs) op).1)
    (hy : ∀ op, 0 < (querySummary scale Q
      (State.compile (softmaxFiniteFactorization scale Q) ys) op).1) :
    State.compile (softmaxFiniteFactorization scale Q) xs
        = State.compile (softmaxFiniteFactorization scale Q) ys
      ↔
    (rawMachine (ν := ν) (softmaxFiniteFactorization scale Q)).equivalent
      (fun _ => True) xs ys := by
  let F := softmaxFiniteFactorization scale Q
  constructor
  · intro h
    exact compiled_eq_implies_all_append_futures_equivalent F h
  · intro heq
    apply (state_eq_iff_fixed_key_all_value_future_reads
      scale Q (State.compile F xs) (State.compile F ys) kstar hx hy).2
    intro op v
    have hfuture := heq [(kstar, v)] trivial
    have hop := congrFun hfuture op
    change State.rawRead F op ((kstar, v) :: xs)
      = State.rawRead F op ((kstar, v) :: ys) at hop
    rw [← State.read_compile_eq_rawRead F op ((kstar, v) :: xs),
        ← State.read_compile_eq_rawRead F op ((kstar, v) :: ys)] at hop
    change State.read F (State.append F (State.compile F xs) kstar v) op
      = State.read F (State.append F (State.compile F ys) kstar v) op at hop
    exact hop

/-- The exact finite-query softmax compiler is a separating realization for
all future append words on any raw-cache domain where the compiled masses are
positive. This is the concrete predictive/Nerode quotient statement. -/
theorem exactRealization_separating_on_positive_mass
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [Nonempty ν]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (kstar : κ → ℝ)
    (P : List ((κ → ℝ) × (ν → ℝ)) → Prop)
    (hpos : ∀ xs, P xs → ∀ op, 0 < (querySummary scale Q
      (State.compile (softmaxFiniteFactorization scale Q) xs) op).1) :
    ∀ xs ys, P xs → P ys →
      (rawMachine (ν := ν) (softmaxFiniteFactorization scale Q)).equivalent
        (fun _ => True) xs ys →
      State.compile (softmaxFiniteFactorization scale Q) xs
        = State.compile (softmaxFiniteFactorization scale Q) ys := by
  intro xs ys hxs hys heq
  exact (compile_eq_iff_all_append_futures_equivalent_positive_mass
    scale Q xs ys kstar (hpos xs hxs) (hpos ys hys)).2 heq

end SoftmaxPredictiveQuotient
end KernelOperational
