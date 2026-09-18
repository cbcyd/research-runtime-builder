import MemoryOperational.SoftmaxContinuousSoftmax
import MemoryOperational.KernelRealization

open Filter Topology

namespace KernelOperational
namespace SoftmaxReachable

open MemoryOperational
open KernelOperational.Realization
open SoftmaxSeparation

/-- The exact compiled kernel-memory state viewed as a deterministic recurrent
machine in its own right. -/
noncomputable def compiledStateMachine
    {Q K ρ ν : Type*} [Fintype ρ]
    (F : Factorization Q K ρ) :
    Machine (State F ν) (Item K ν) (Q → ν → ℝ) where
  step x item := State.append F x item.1 item.2
  observe x := fun q => State.read F x q

/-- A finite-dimensional exact recurrent realization of the compiled kernel
machine whose state encoder is continuous. -/
structure ContinuousCompiledRealization
    {Q K ρ ν : Type*} [Fintype ρ]
    (F : Factorization Q K ρ) (d : ℕ) where
  realization :
    MemoryOperational.Realization
      (compiledStateMachine (ν := ν) F) (Fin d → ℝ)
  continuous_compile : Continuous realization.compile

/-- The rich softmax summary parameterization is globally continuous. -/
theorem richSummaryMap_continuous
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ) :
    Continuous (richSummaryMap (ν := ν) c lambda) := by
  unfold richSummaryMap
  fun_prop

/-- Every continuous exact recurrent realization of the finite-query softmax
summary machine induces the physical one-append/one-query probe realization
used by the continuous-minimality lower bound. -/
noncomputable def ContinuousCompiledRealization.toPhysicalProbeRealization
    {m kdim d : ℕ} {ν : Type*} [Fintype ν]
    (scale : ℝ) (Q : Fin m → Fin kdim → ℝ)
    (c lambda : Fin m → ℝ)
    (kstar : Fin kdim → ℝ)
    (R : ContinuousCompiledRealization (ν := ν)
      (softmaxFiniteFactorization scale Q) d) :
    ContinuousExactPhysicalProbeRealization m d ν c lambda
      (fun op => Real.exp (scale * ∑ a, Q op a * kstar a)) where
  state x := R.realization.compile (richSummaryMap (ν := ν) c lambda x)
  observe z op v :=
    R.realization.observe
      (R.realization.step z (kstar, v)) op
  continuous_state :=
    R.continuous_compile.comp (richSummaryMap_continuous c lambda)
  exact_probe := by
    intro x op v
    let F := softmaxFiniteFactorization scale Q
    have hstep := R.realization.step_commute
      (richSummaryMap (ν := ν) c lambda x) (kstar, v)
    have hobs := R.realization.observe_commute
      (State.append F (richSummaryMap (ν := ν) c lambda x) kstar v)
    change
      R.realization.observe
          (R.realization.step
            (R.realization.compile (richSummaryMap (ν := ν) c lambda x))
            (kstar, v)) op
        =
      tangentProbeRead
        (fun op => Real.exp (scale * ∑ a, Q op a * kstar a))
        (richSummaryMap (ν := ν) c lambda x) op v
    rw [← hstep]
    change
      R.realization.observe
          (R.realization.compile
            (State.append F
              (richSummaryMap (ν := ν) c lambda x) kstar v)) op
        =
      tangentProbeRead
        (fun op => Real.exp (scale * ∑ a, Q op a * kstar a))
        (richSummaryMap (ν := ν) c lambda x) op v
    have hop := congrFun hobs op
    rw [← hop]
    change
      State.read F
          (State.append F (richSummaryMap (ν := ν) c lambda x) kstar v) op
        =
      tangentProbeRead
        (fun op => Real.exp (scale * ∑ a, Q op a * kstar a))
        (richSummaryMap (ν := ν) c lambda x) op v
    rw [softmax_read_eq_querySummary]
    rw [querySummary_append]
    rfl

/-- Conditional lower bound for genuine continuous exact recurrent
realizations of the finite-query softmax compiled-state machine.

This closes the recurrent-realization-to-embedding part of the argument:
after restricting any such recurrent realization to the physically reachable
rich line-cache family, predictive separation makes its continuous state
encoder locally injective. The only external premise is the standard
open-injection dimension obstruction. -/
theorem continuous_compiled_softmax_dimension_lower_bound_of_open_obstruction
    {m kdim d : ℕ} {ν : Type*}
    [Fintype ν] [Nonempty ν] [Nonempty (Fin m)]
    (hTop : OpenInjectionDimensionObstruction
      (SummaryTangent m ν) (Fin d → ℝ))
    (scale : ℝ) (hscale : scale ≠ 0)
    (Q : Fin m → Fin kdim → ℝ)
    (hQ : Function.Injective Q)
    (hQ0 : ∀ i, Q i ≠ 0)
    (R : ContinuousCompiledRealization
      (softmaxFiniteFactorization scale Q) d) :
    m * (1 + Fintype.card ν) ≤ d := by
  rcases exists_nonzero_separating_direction_for_softmax
    scale hscale Q hQ hQ0 with ⟨u, hu0, huinj⟩
  let k0 : Fin kdim → ℝ := fun _ => 0
  let kstar : Fin kdim → ℝ := fun _ => 0
  let c : Fin m → ℝ := fun j => lineBaseFactor scale Q k0 j
  let lambda : Fin m → ℝ := fun j => lineSlope scale Q u j
  let cstar : Fin m → ℝ :=
    fun j => Real.exp (scale * ∑ a, Q j a * kstar a)
  let P :=
    R.toPhysicalProbeRealization scale Q c lambda kstar
  apply P.dimension_lower_bound_of_open_obstruction
    hTop c lambda cstar
  · intro j
    exact Real.exp_pos _
  · intro j
    have hj := hu0 j
    simpa [lambda, lineSlope, lineExponents] using hj
  · intro i j hij
    apply huinj
    change scale * ∑ a, Q i a * u a =
      scale * ∑ a, Q j a * u a
    simpa [lambda, lineSlope, lineExponents] using hij
  · intro j
    exact Real.exp_pos _

end SoftmaxReachable
end KernelOperational
