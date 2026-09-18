import MemoryOperational.SoftmaxPhysicalBridge
import MemoryOperational.SoftmaxLocalInverse

open BigOperators Filter Topology

namespace KernelOperational
namespace SoftmaxReachable

/-- Polynomial encoding of one query vector along the power-curve direction. -/
noncomputable def queryProjectionPolynomial
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (i : Fin n) : Polynomial ℝ :=
  ∑ a : Fin d, Polynomial.monomial (a : ℕ) (Q i a)

@[simp] theorem queryProjectionPolynomial_coeff
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (i : Fin n) (a : Fin d) :
    (queryProjectionPolynomial Q i).coeff (a : ℕ) = Q i a := by
  simp only [queryProjectionPolynomial, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : (b : ℕ) ≠ (a : ℕ) := by
      intro h
      exact hba (Fin.ext h)
    simp [hne]
  · simp

/-- A nonzero query vector gives a nonzero projection polynomial. -/
theorem queryProjectionPolynomial_ne_zero
    {n d : ℕ} (Q : Fin n → Fin d → ℝ)
    (hQ0 : ∀ i, Q i ≠ 0) (i : Fin n) :
    queryProjectionPolynomial Q i ≠ 0 := by
  intro hp
  apply hQ0 i
  funext a
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (a : ℕ)) hp
  rw [queryProjectionPolynomial_coeff] at hc
  simpa using hc

/-- Evaluation of the query polynomial is its projection on the power curve. -/
theorem eval_queryProjectionPolynomial
    {n d : ℕ} (Q : Fin n → Fin d → ℝ) (i : Fin n) (t : ℝ) :
    Polynomial.eval t (queryProjectionPolynomial Q i)
      = ∑ a : Fin d, Q i a * powerDirection t a := by
  simp [queryProjectionPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial, powerDirection]

/-- A finite family of pairwise distinct nonzero queries admits one power-curve
direction on which all projections are pairwise distinct and all are nonzero. -/
theorem exists_powerDirection_nonzero_separates_queries
    {n d : ℕ} (Q : Fin n → Fin d → ℝ)
    (hQ : Function.Injective Q)
    (hQ0 : ∀ i, Q i ≠ 0) :
    ∃ t : ℝ,
      (∀ i : Fin n, (∑ a, Q i a * powerDirection t a) ≠ 0) ∧
      Function.Injective (fun i : Fin n =>
        ∑ a, Q i a * powerDirection t a) := by
  have hnonzero : ∀ᶠ t : ℝ in Filter.cofinite,
      ∀ i : Fin n, Polynomial.eval t (queryProjectionPolynomial Q i) ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hp := Polynomial.eventually_cofinite_not_isRoot
      (queryProjectionPolynomial_ne_zero Q hQ0 i)
    filter_upwards [hp] with t ht
    simpa [Polynomial.IsRoot] using ht
  have hsep : ∀ᶠ t : ℝ in Filter.cofinite,
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
  rcases (hnonzero.and hsep).exists with ⟨t, ht0, htsep⟩
  refine ⟨t, ?_, ?_⟩
  · intro i
    have hi := ht0 i
    rw [eval_queryProjectionPolynomial] at hi
    exact hi
  · intro i j hijproj
    by_contra hij
    have hne := htsep i j hij
    rw [eval_queryDifferencePolynomial] at hne
    apply hne
    have hzero :
        (∑ a, Q i a * powerDirection t a) -
          (∑ a, Q j a * powerDirection t a) = 0 :=
      sub_eq_zero.mpr hijproj
    calc
      (∑ a : Fin d, (Q i a - Q j a) * t ^ (a : ℕ))
          =
        (∑ a : Fin d, Q i a * powerDirection t a) -
          (∑ a : Fin d, Q j a * powerDirection t a) := by
            simp [powerDirection, sub_mul, Finset.sum_sub_distrib]
      _ = 0 := hzero

/-- With nonzero softmax scale, a finite injective nonzero query family admits
a key direction whose softmax line exponents are pairwise distinct and nonzero. -/
theorem exists_nonzero_separating_direction_for_softmax
    {n d : ℕ} (scale : ℝ) (hscale : scale ≠ 0)
    (Q : Fin n → Fin d → ℝ)
    (hQ : Function.Injective Q)
    (hQ0 : ∀ i, Q i ≠ 0) :
    ∃ u : Fin d → ℝ,
      (∀ i : Fin n, lineExponents scale Q u i ≠ 0) ∧
      Function.Injective (lineExponents scale Q u) := by
  rcases exists_powerDirection_nonzero_separates_queries Q hQ hQ0 with
    ⟨t, ht0, htinj⟩
  refine ⟨powerDirection t, ?_, ?_⟩
  · intro i
    exact mul_ne_zero hscale (ht0 i)
  · intro i j hij
    apply htinj
    apply mul_left_cancel₀ hscale
    simpa [lineExponents] using hij

/-- Generic physical local-open-image theorem for finite ordinary softmax:
distinct nonzero queries and nonzero scale have a physical key-line direction
for which the complete m-item cache-to-(Z,M) summary map is locally invertible
at the Vandermonde witness. -/
theorem exists_softmaxLineCacheSummary_map_nhds_eq
    {m d : ℕ} {ν : Type*} [Fintype ν]
    (scale : ℝ) (hscale : scale ≠ 0)
    (Q : Fin m → Fin d → ℝ)
    (hQ : Function.Injective Q)
    (hQ0 : ∀ i, Q i ≠ 0)
    (k0 : Fin d → ℝ) :
    ∃ u : Fin d → ℝ,
      Filter.map (softmaxLineCacheSummary (ν := ν) scale Q k0 u)
          (𝓝 (richSummaryBase m ν))
        =
      𝓝 (softmaxLineCacheSummary (ν := ν) scale Q k0 u
          (richSummaryBase m ν)) := by
  rcases exists_nonzero_separating_direction_for_softmax
    scale hscale Q hQ hQ0 with ⟨u, hu0, huinj⟩
  refine ⟨u, ?_⟩
  have hslope0 :
      ∀ i : Fin m, lineSlope scale Q u i ≠ 0 := by
    simpa [lineSlope, lineExponents] using hu0
  have hslopeinj :
      Function.Injective (lineSlope scale Q u) := by
    intro i j hij
    apply huinj
    change scale * ∑ a, Q i a * u a =
      scale * ∑ a, Q j a * u a
    simpa [lineSlope] using hij
  have hc :
      ∀ i : Fin m, lineBaseFactor scale Q k0 i ≠ 0 := by
    intro i
    exact Real.exp_ne_zero _
  have hlocal := richSummaryMap_map_nhds_eq
    (ν := ν)
    (fun i => lineBaseFactor scale Q k0 i)
    (fun i => lineSlope scale Q u i)
    hc hslope0 hslopeinj
  have hfun :
      softmaxLineCacheSummary (ν := ν) scale Q k0 u =
        richSummaryMap
          (fun i => lineBaseFactor scale Q k0 i)
          (fun i => lineSlope scale Q u i) := by
    funext x
    exact softmaxLineCacheSummary_eq_richSummaryMap_fin
      scale Q k0 u x
  rw [hfun]
  exact hlocal

end SoftmaxReachable
end KernelOperational
