import MemoryOperational.SoftmaxContinuousBoundary
import MemoryOperational.SoftmaxSeparation

open Filter Topology Set BigOperators

namespace KernelOperational
namespace SoftmaxReachable

open SoftmaxSeparation

/-- One declared query coordinate of a rich softmax summary. -/
def tangentQuerySummary
    {m : ℕ} {ν : Type*}
    (x : SummaryTangent m ν) (op : Fin m) : QuerySummary ν :=
  (x.1 op, fun a => x.2 a op)

/-- The separating one-append/one-query probe written directly on rich summary
coordinates. The future key contributes the positive query-specific weight
cstar op, while its future value is freely varied. -/
noncomputable def tangentProbeRead
    {m : ℕ} {ν : Type*}
    (cstar : Fin m → ℝ)
    (x : SummaryTangent m ν)
    (op : Fin m) (v : ν → ℝ) : ν → ℝ :=
  summaryRead (appendSummary (tangentQuerySummary x op) (cstar op) v)

/-- Positive rich summaries are exactly separated by the fixed-key,
arbitrary-value probe family. -/
theorem tangent_eq_iff_all_probe_reads
    {m : ℕ} {ν : Type*} [Nonempty ν]
    (x y : SummaryTangent m ν)
    (cstar : Fin m → ℝ)
    (hx : ∀ op, 0 < x.1 op)
    (hy : ∀ op, 0 < y.1 op)
    (hcstar : ∀ op, 0 < cstar op) :
    x = y ↔
      ∀ op (v : ν → ℝ),
        tangentProbeRead cstar x op v =
          tangentProbeRead cstar y op v := by
  constructor
  · intro h op v
    cases h
    rfl
  · intro h
    have hsummary : ∀ op,
        tangentQuerySummary x op = tangentQuerySummary y op := by
      intro op
      apply (summary_eq_iff_all_positive_weight_append_reads
        (tangentQuerySummary x op) (tangentQuerySummary y op) (cstar op)
        (hx op) (hy op) (hcstar op)).2
      intro v
      exact h op v
    apply Prod.ext
    · funext op
      exact congrArg Prod.fst (hsummary op)
    · funext a op
      have hm := congrArg Prod.snd (hsummary op)
      exact congrFun hm a

/-- The physical rich-summary map has strictly positive mass coordinates when
the fixed base softmax factors are positive and the cache family is nonempty. -/
theorem richSummaryMap_mass_pos
    {m : ℕ} {ν : Type*} [Fintype ν] [Nonempty (Fin m)]
    (c lambda : Fin m → ℝ)
    (hc : ∀ op, 0 < c op)
    (x : SummaryTangent m ν) (op : Fin m) :
    0 < (richSummaryMap (ν := ν) c lambda x).1 op := by
  change 0 < c op * ∑ t : Fin m, Real.exp (lambda op * x.1 t)
  exact mul_pos (hc op)
    (Finset.sum_pos (fun t ht => Real.exp_pos _) Finset.univ_nonempty)

/-- A continuous exact probe realization of a physical rich-cache family.

The proposed state has d real coordinates. Its observer must reproduce every
separating one-append/one-query probe of the ordinary softmax summary. No
continuity of the observer is required; only the physical-parameter to state
map is assumed continuous. -/
structure ContinuousExactPhysicalProbeRealization
    (m d : ℕ) (ν : Type*) [Fintype ν]
    (c lambda cstar : Fin m → ℝ) where
  state : SummaryTangent m ν → (Fin d → ℝ)
  observe : (Fin d → ℝ) → Fin m → (ν → ℝ) → (ν → ℝ)
  continuous_state : Continuous state
  exact_probe :
    ∀ x op (v : ν → ℝ),
      observe (state x) op v =
        tangentProbeRead cstar (richSummaryMap (ν := ν) c lambda x) op v

/-- Equality of exact realization states forces equality of physical softmax
summaries, because the declared probe language separates positive summaries. -/
theorem ContinuousExactPhysicalProbeRealization.summary_eq_of_state_eq
    {m d : ℕ} {ν : Type*}
    [Fintype ν] [Nonempty ν] [Nonempty (Fin m)]
    (c lambda cstar : Fin m → ℝ)
    (hc : ∀ op, 0 < c op)
    (hcstar : ∀ op, 0 < cstar op)
    (R : ContinuousExactPhysicalProbeRealization m d ν c lambda cstar)
    {x y : SummaryTangent m ν}
    (hstate : R.state x = R.state y) :
    richSummaryMap (ν := ν) c lambda x =
      richSummaryMap (ν := ν) c lambda y := by
  apply (tangent_eq_iff_all_probe_reads
    (richSummaryMap (ν := ν) c lambda x)
    (richSummaryMap (ν := ν) c lambda y)
    cstar
    (richSummaryMap_mass_pos c lambda hc x)
    (richSummaryMap_mass_pos c lambda hc y)
    hcstar).2
  intro op v
  calc
    tangentProbeRead cstar (richSummaryMap (ν := ν) c lambda x) op v
        = R.observe (R.state x) op v := (R.exact_probe x op v).symm
    _ = R.observe (R.state y) op v := by rw [hstate]
    _ = tangentProbeRead cstar
        (richSummaryMap (ν := ν) c lambda y) op v := R.exact_probe y op v

/-- On the inverse-function source neighborhood, a continuous exact physical
probe realization is injective in the physical cache parameters. This is the
realization-to-embedding bridge required by the continuous minimality proof. -/
theorem ContinuousExactPhysicalProbeRealization.local_injOn
    {m d : ℕ} {ν : Type*}
    [Fintype ν] [Nonempty ν] [Nonempty (Fin m)]
    (c lambda cstar : Fin m → ℝ)
    (hc : ∀ op, 0 < c op)
    (hlambda0 : ∀ op, lambda op ≠ 0)
    (hlambdaInj : Function.Injective lambda)
    (hcstar : ∀ op, 0 < cstar op)
    (R : ContinuousExactPhysicalProbeRealization m d ν c lambda cstar) :
    let hder :=
      richSummaryMap_hasStrictFDerivAt_equiv
        (ν := ν) c lambda (fun j => ne_of_gt (hc j)) hlambda0 hlambdaInj
    Set.InjOn R.state
      (hder.toOpenPartialHomeomorph
        (richSummaryMap (ν := ν) c lambda)).source := by
  dsimp
  let hder :=
    richSummaryMap_hasStrictFDerivAt_equiv
      (ν := ν) c lambda (fun j => ne_of_gt (hc j)) hlambda0 hlambdaInj
  let e := hder.toOpenPartialHomeomorph
    (richSummaryMap (ν := ν) c lambda)
  intro x hx y hy hstate
  apply e.injOn hx hy
  exact R.summary_eq_of_state_eq c lambda cstar hc hcstar hstate

/-- Conditional arbitrary-continuous state lower bound.

The project-specific realization-to-embedding bridge is now explicit: exact
probe behavior plus predictive separation makes the continuous state map
injective on the nonempty open inverse-function source neighborhood. The only
remaining external hypothesis is the standard finite-dimensional topological
open-injection obstruction. -/
theorem ContinuousExactPhysicalProbeRealization.dimension_lower_bound_of_open_obstruction
    {m d : ℕ} {ν : Type*}
    [Fintype ν] [Nonempty ν] [Nonempty (Fin m)]
    (hTop : OpenInjectionDimensionObstruction)
    (c lambda cstar : Fin m → ℝ)
    (hc : ∀ op, 0 < c op)
    (hlambda0 : ∀ op, lambda op ≠ 0)
    (hlambdaInj : Function.Injective lambda)
    (hcstar : ∀ op, 0 < cstar op)
    (R : ContinuousExactPhysicalProbeRealization m d ν c lambda cstar) :
    m * (1 + Fintype.card ν) ≤ d := by
  let hder :=
    richSummaryMap_hasStrictFDerivAt_equiv
      (ν := ν) c lambda (fun j => ne_of_gt (hc j)) hlambda0 hlambdaInj
  let e := hder.toOpenPartialHomeomorph
    (richSummaryMap (ν := ν) c lambda)
  let U : Set (SummaryTangent m ν) := e.source
  have hUopen : IsOpen U := e.open_source
  have hUne : U.Nonempty := by
    exact ⟨richSummaryBase m ν, hder.mem_toOpenPartialHomeomorph_source⟩
  let f : U → (Fin d → ℝ) := fun x => R.state x.1
  have hfcont : Continuous f := R.continuous_state.comp continuous_subtype_val
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact R.local_injOn c lambda cstar hc hlambda0 hlambdaInj hcstar
      x.property y.property hxy
  have hdim :
      Module.finrank ℝ (SummaryTangent m ν) ≤
        Module.finrank ℝ (Fin d → ℝ) :=
    hTop (E := SummaryTangent m ν) (F := Fin d → ℝ)
      U hUopen hUne f hfcont hfinj
  rw [summaryTangent_finrank, Module.finrank_fin_fun] at hdim
  exact hdim

end SoftmaxReachable
end KernelOperational
