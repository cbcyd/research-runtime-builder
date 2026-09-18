import MemoryOperational.KernelRealization

namespace KernelOperational
namespace SoftmaxSeparation

/-- Per-query normalized-attention summary coordinates. -/
abbrev QuerySummary (ν : Type*) := ℝ × (ν → ℝ)

/-- Append a future item whose weight at this query is `c`. -/
def appendSummary {ν : Type*}
    (s : QuerySummary ν) (c : ℝ) (v : ν → ℝ) : QuerySummary ν :=
  (s.1 + c, s.2 + c • v)

/-- Normalized read of one per-query summary. -/
noncomputable def summaryRead {ν : Type*} (s : QuerySummary ν) : ν → ℝ :=
  fun j => s.2 j / s.1

/-- One positive-weight future append with arbitrary value separates a positive
per-query summary exactly. This is the algebraic core of the rich-future
minimality argument. -/
theorem summary_eq_iff_all_positive_weight_append_reads
    {ν : Type*} [Nonempty ν]
    (s t : QuerySummary ν) (c : ℝ)
    (hs : 0 < s.1) (ht : 0 < t.1) (hc : 0 < c) :
    s = t ↔ ∀ v : ν → ℝ,
      summaryRead (appendSummary s c v) = summaryRead (appendSummary t c v) := by
  constructor
  · intro h v
    cases h
    rfl
  · intro h
    let j0 : ν := Classical.choice (inferInstance : Nonempty ν)
    let z : ν → ℝ := fun _ => 0
    let o : ν → ℝ := fun _ => 1
    have hsz : s.1 + c ≠ 0 := ne_of_gt (add_pos hs hc)
    have htz : t.1 + c ≠ 0 := ne_of_gt (add_pos ht hc)
    have hz := congrFun (h z) j0
    have ho := congrFun (h o) j0
    dsimp [summaryRead, appendSummary, z, o] at hz ho
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero,
      mul_one] at hz ho
    field_simp [hsz, htz] at hz ho
    have hmass : s.1 = t.1 := by
      have hc0 : c ≠ 0 := ne_of_gt hc
      have hprod : c * (t.1 - s.1) = 0 := by
        nlinarith [hz, ho]
      have : t.1 - s.1 = 0 := (mul_eq_zero.mp hprod).resolve_left hc0
      linarith
    apply Prod.ext
    · exact hmass
    · funext j
      have hj := congrFun (h z) j
      dsimp [summaryRead, appendSummary, z] at hj
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero] at hj
      rw [hmass] at hj
      have hden : t.1 + c ≠ 0 := htz
      field_simp [hden] at hj
      exact hj

/-- Extract one query's `(Z,M)` coordinates from a finite-query feature state. -/
def querySummary
    {σ κ ν : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (x : State (softmaxFiniteFactorization scale Q) ν) (op : σ) : QuerySummary ν :=
  (x.1 op, fun j => x.2 j op)

/-- In the one-hot finite-query factorization, the generic normalized kernel
read is exactly the corresponding per-query `(Z,M)` read. -/
theorem softmax_read_eq_querySummary
    {σ κ ν : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (x : State (softmaxFiniteFactorization scale Q) ν) (op : σ) :
    State.read (softmaxFiniteFactorization scale Q) x op
      = summaryRead (querySummary scale Q x op) := by
  funext j
  classical
  simp [State.read, State.numer, State.denom, softmaxFiniteFactorization,
    summaryRead, querySummary]

/-- Query-summary extraction commutes exactly with appending one physical KV
item. The query-specific append weight is the true softmax exponential weight. -/
theorem querySummary_append
    {σ κ ν : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (x : State (softmaxFiniteFactorization scale Q) ν)
    (op : σ) (k : κ → ℝ) (v : ν → ℝ) :
    querySummary scale Q
      (State.append (softmaxFiniteFactorization scale Q) x k v) op
      = appendSummary (querySummary scale Q x op)
          (Real.exp (scale * ∑ j, Q op j * k j)) v := by
  apply Prod.ext
  · rfl
  · funext j
    simp [querySummary, State.append, appendSummary, softmaxFiniteFactorization, smul_eq_mul]
    ring

/-- A single fixed future key plus arbitrary future value, followed by any
query in the declared finite family, separates the entire finite-query softmax
state exactly on the positive-mass domain. -/
theorem state_eq_iff_fixed_key_all_value_future_reads
    {σ κ ν : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype κ] [Nonempty ν]
    (scale : ℝ) (Q : σ → κ → ℝ)
    (x y : State (softmaxFiniteFactorization scale Q) ν)
    (kstar : κ → ℝ)
    (hx : ∀ op, 0 < (querySummary scale Q x op).1)
    (hy : ∀ op, 0 < (querySummary scale Q y op).1) :
    x = y ↔ ∀ op (v : ν → ℝ),
      State.read (softmaxFiniteFactorization scale Q)
          (State.append (softmaxFiniteFactorization scale Q) x kstar v) op
        = State.read (softmaxFiniteFactorization scale Q)
          (State.append (softmaxFiniteFactorization scale Q) y kstar v) op := by
  constructor
  · intro h op v
    cases h
    rfl
  · intro h
    have hsummary : ∀ op,
        querySummary scale Q x op = querySummary scale Q y op := by
      intro op
      let c := Real.exp (scale * ∑ j, Q op j * kstar j)
      have hc : 0 < c := Real.exp_pos _
      apply (summary_eq_iff_all_positive_weight_append_reads
        (querySummary scale Q x op) (querySummary scale Q y op) c
        (hx op) (hy op) hc).2
      intro v
      have hop := h op v
      rw [softmax_read_eq_querySummary, softmax_read_eq_querySummary] at hop
      rw [querySummary_append, querySummary_append] at hop
      exact hop
    apply Prod.ext
    · funext op
      exact congrArg Prod.fst (hsummary op)
    · funext j op
      have hm := congrArg Prod.snd (hsummary op)
      exact congrFun hm j

end SoftmaxSeparation
end KernelOperational
