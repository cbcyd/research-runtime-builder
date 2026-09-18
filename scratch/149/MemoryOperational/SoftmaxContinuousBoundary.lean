import MemoryOperational.SoftmaxGenericLocalOpen
import Mathlib.LinearAlgebra.Dimension.Constructions

open Filter Topology Set

namespace KernelOperational
namespace SoftmaxReachable

universe u v

/-- The only external topology principle still missing from the pinned Mathlib:
a continuous injection from a nonempty open subset of one finite-dimensional
real normed space into another cannot lower dimension.

This is a proposition, not an axiom. The final softmax theorem below takes it
as an explicit hypothesis, isolating the exact standard-topology dependency. -/
def OpenInjectionDimensionObstruction
    (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] : Prop :=
  ∀ U : Set E,
    IsOpen U →
    U.Nonempty →
    ∀ f : U → F,
      Continuous f →
      Function.Injective f →
      Module.finrank ℝ E ≤ Module.finrank ℝ F

/-- Local invertibility implies that the full physical rich-summary range is
itself a neighborhood of the witness summary (not necessarily open globally,
but it contains an open neighborhood). -/
theorem richSummaryMap_range_mem_nhds
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    Set.range (richSummaryMap (ν := ν) c lambda) ∈
      𝓝 (richSummaryMap (ν := ν) c lambda (richSummaryBase m ν)) := by
  rw [← richSummaryMap_map_nhds_eq c lambda hc hlambda0 hlambdaInj]
  rw [Filter.mem_map]
  simp

/-- Therefore the physically reachable rich-summary range contains a nonempty
open subset of the full summary-coordinate space. -/
theorem exists_nonempty_open_subset_range_richSummaryMap
    {m : ℕ} {ν : Type*} [Fintype ν]
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda) :
    ∃ U : Set (SummaryTangent m ν),
      IsOpen U ∧ U.Nonempty ∧
      U ⊆ Set.range (richSummaryMap (ν := ν) c lambda) := by
  have hnhds :=
    richSummaryMap_range_mem_nhds
      (ν := ν) c lambda hc hlambda0 hlambdaInj
  rcases mem_nhds_iff.mp hnhds with ⟨U, hUsub, hUopen, hUmem⟩
  exact ⟨U, hUopen, ⟨_, hUmem⟩, hUsub⟩

/-- Conditional final continuous-state lower bound.

All softmax-specific premises are machine-checked: the rich physical cache
family has a nonempty open reachable summary set. If encode is continuous
and behaviorally separating on the physically reachable summary range, then
the standard open-injection dimension obstruction forces at least
m * (D_v + 1) real state coordinates.

The only non-project hypothesis is OpenInjectionDimensionObstruction. -/
theorem continuous_state_dimension_lower_bound_of_open_obstruction
    {m d : ℕ} {ν : Type*} [Fintype ν]
    (hTop : OpenInjectionDimensionObstruction
      (SummaryTangent m ν) (Fin d → ℝ))
    (c lambda : Fin m → ℝ)
    (hc : ∀ j, c j ≠ 0)
    (hlambda0 : ∀ j, lambda j ≠ 0)
    (hlambdaInj : Function.Injective lambda)
    (encode : SummaryTangent m ν → (Fin d → ℝ))
    (hcont : Continuous encode)
    (hinj : Set.InjOn encode
      (Set.range (richSummaryMap (ν := ν) c lambda))) :
    m * (1 + Fintype.card ν) ≤ d := by
  rcases exists_nonempty_open_subset_range_richSummaryMap
    (ν := ν) c lambda hc hlambda0 hlambdaInj with
    ⟨U, hUopen, hUne, hUsub⟩
  let f : U → (Fin d → ℝ) := fun x => encode x.1
  have hfcont : Continuous f := hcont.comp continuous_subtype_val
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hinj (hUsub x.property) (hUsub y.property) hxy
  have hdim :
      Module.finrank ℝ (SummaryTangent m ν) ≤
        Module.finrank ℝ (Fin d → ℝ) :=
    hTop U hUopen hUne f hfcont hfinj
  rw [summaryTangent_finrank, Module.finrank_fin_fun] at hdim
  exact hdim

end SoftmaxReachable
end KernelOperational
