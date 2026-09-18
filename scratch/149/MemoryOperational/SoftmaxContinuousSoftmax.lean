import MemoryOperational.SoftmaxContinuousRealization
import MemoryOperational.SoftmaxGenericLocalOpen
import MemoryOperational.SoftmaxPhysicalBridge

open BigOperators

namespace KernelOperational
namespace SoftmaxReachable

/-- Ordinary-softmax specialization of the conditional continuous-state lower
bound. For every finite injective family of nonzero queries at nonzero scale,
there exists one physical key-line direction such that every continuous exact
probe realization of that line-cache family needs at least m(D_v+1) real
coordinates, assuming only the standard open-injection dimension obstruction.

The fixed future probe key kstar is arbitrary: its softmax weights are
automatically strictly positive. -/
theorem exists_direction_continuous_exact_softmax_probe_dimension_lower_bound
    {m d kdim : ℕ} {ν : Type*}
    [Fintype ν] [Nonempty ν] [Nonempty (Fin m)]
    (hTop : OpenInjectionDimensionObstruction
      (SummaryTangent m ν) (Fin d → ℝ))
    (scale : ℝ) (hscale : scale ≠ 0)
    (Q : Fin m → Fin kdim → ℝ)
    (hQ : Function.Injective Q)
    (hQ0 : ∀ i, Q i ≠ 0)
    (k0 kstar : Fin kdim → ℝ) :
    ∃ u : Fin kdim → ℝ,
      ∀ R : ContinuousExactPhysicalProbeRealization m d ν
        (fun j => lineBaseFactor scale Q k0 j)
        (fun j => lineSlope scale Q u j)
        (fun j => Real.exp (scale * ∑ a, Q j a * kstar a)),
        m * (1 + Fintype.card ν) ≤ d := by
  rcases exists_nonzero_separating_direction_for_softmax
    scale hscale Q hQ hQ0 with ⟨u, hu0, huinj⟩
  refine ⟨u, ?_⟩
  intro R
  apply R.dimension_lower_bound_of_open_obstruction
    hTop
    (fun j => lineBaseFactor scale Q k0 j)
    (fun j => lineSlope scale Q u j)
    (fun j => Real.exp (scale * ∑ a, Q j a * kstar a))
  · intro j
    exact Real.exp_pos _
  · intro j
    have hj := hu0 j
    simpa [lineSlope, lineExponents] using hj
  · intro i j hij
    apply huinj
    change scale * ∑ a, Q i a * u a =
      scale * ∑ a, Q j a * u a
    simpa [lineSlope, lineExponents] using hij
  · intro j
    exact Real.exp_pos _

end SoftmaxReachable
end KernelOperational
