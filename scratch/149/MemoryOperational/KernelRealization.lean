import OfflineBundle.BundleImports
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Card
import MemoryOperational.OperationalQuotient

open BigOperators Matrix

namespace KernelOperational

/-- Exact finite feature factorization of a normalized attention kernel on a
specified query/key domain. -/
structure Factorization (Q K ρ : Type*) [Fintype ρ] where
  kernel : Q → K → ℝ
  phi : K → ρ → ℝ
  psi : Q → ρ → ℝ
  exact : ∀ q k, kernel q k = ∑ r, psi q r * phi k r

/-- Exact recurrent sufficient state: denominator feature sum and value-feature
moments. It is deliberately a linear coordinate space. -/
abbrev State {Q K ρ : Type*} [Fintype ρ]
    (F : Factorization Q K ρ) (ν : Type*) :=
  (ρ → ℝ) × (ν → ρ → ℝ)

namespace State

variable {Q K ρ ν : Type*} [Fintype ρ] (F : Factorization Q K ρ)

/-- Append one raw key/value item. -/
def append (x : State F ν) (k : K) (v : ν → ℝ) : State F ν :=
  (x.1 + F.phi k, fun j r => x.2 j r + v j * F.phi k r)

/-- Compile a finite raw cache by recurrent append. -/
def compile : List (K × (ν → ℝ)) → State F ν
  | [] => 0
  | item :: rest => append F (compile rest) item.1 item.2

/-- Denominator exposed to one legal query. -/
def denom (x : State F ν) (q : Q) : ℝ :=
  ∑ r, F.psi q r * x.1 r

/-- Unnormalized value numerator exposed to one legal query. -/
def numer (x : State F ν) (q : Q) : ν → ℝ :=
  fun j => ∑ r, F.psi q r * x.2 j r

/-- Normalized exact kernel-attention readout. -/
noncomputable def read (x : State F ν) (q : Q) : ν → ℝ :=
  fun j => numer F x q j / denom F x q

@[simp] theorem denom_zero (q : Q) : denom F (0 : State F ν) q = 0 := by
  simp [denom]

@[simp] theorem numer_zero (q : Q) : numer F (0 : State F ν) q = 0 := by
  funext j
  simp [numer]

/-- One append updates the denominator by exactly the kernel weight. -/
theorem denom_append (x : State F ν) (q : Q) (k : K) (v : ν → ℝ) :
    denom F (append F x k v) q = denom F x q + F.kernel q k := by
  rw [F.exact]
  simp_rw [denom, append, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

/-- One append updates the numerator by kernel-weighted value. -/
theorem numer_append (x : State F ν) (q : Q) (k : K) (v : ν → ℝ) :
    numer F (append F x k v) q = numer F x q + F.kernel q k • v := by
  funext j
  rw [F.exact]
  simp only [numer, append, Pi.add_apply, smul_eq_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ r, F.psi q r * (v j * F.phi k r))
        = ∑ r, (F.psi q r * F.phi k r) * v j := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
    _ = (∑ r, F.psi q r * F.phi k r) * v j := by
          simpa using (Finset.sum_mul Finset.univ
            (fun r => F.psi q r * F.phi k r) (v j)).symm

/-- Raw cache denominator for comparison with the compiled state. -/
def rawDenom (q : Q) (items : List (K × (ν → ℝ))) : ℝ :=
  (items.map (fun item => F.kernel q item.1)).sum

/-- Raw cache numerator for comparison with the compiled state. -/
def rawNumer (q : Q) (items : List (K × (ν → ℝ))) : ν → ℝ :=
  fun j => (items.map (fun item => F.kernel q item.1 * item.2 j)).sum

/-- Ordinary normalized kernel-attention read on the raw cache. -/
noncomputable def rawRead (q : Q) (items : List (K × (ν → ℝ))) : ν → ℝ :=
  fun j => rawNumer F q items j / rawDenom F q items

/-- Compilation reproduces the exact raw denominator. -/
theorem compile_denom (q : Q) (items : List (K × (ν → ℝ))) :
    denom F (compile F items) q = rawDenom F q items := by
  induction items with
  | nil => simp [compile, rawDenom]
  | cons item rest ih =>
      rw [compile, denom_append, ih]
      simp [rawDenom, add_comm]

/-- Compilation reproduces the exact raw numerator. -/
theorem compile_numer (q : Q) (items : List (K × (ν → ℝ))) :
    numer F (compile F items) q = rawNumer F q items := by
  induction items with
  | nil =>
      funext j
      simp [compile, rawNumer]
  | cons item rest ih =>
      rw [compile, numer_append, ih]
      funext j
      simp [rawNumer, smul_eq_mul, add_comm]

/-- Exact recurrentization theorem: finite factorization yields a causal finite
state whose read is ordinary normalized kernel attention, with no approximation. -/
theorem read_compile_eq_rawRead (q : Q) (items : List (K × (ν → ℝ))) :
    read F (compile F items) q = rawRead F q items := by
  funext j
  simp only [read, rawRead]
  rw [compile_numer, compile_denom]

/-- Augment denominator and value moments into one matrix state. -/
def toMatrix (x : State F ν) : Matrix (Sum Unit ν) ρ ℝ
  | Sum.inl _, r => x.1 r
  | Sum.inr j, r => x.2 j r

/-- Augmented value used by the affine rank-one memory representation. -/
def augValue (v : ν → ℝ) : Sum Unit ν → ℝ
  | Sum.inl _ => 1
  | Sum.inr j => v j

/-- Exact affine-memory bridge: every raw kernel-attention append is one
identity-transport rank-one write in the augmented state. -/
theorem append_toMatrix (x : State F ν) (k : K) (v : ν → ℝ) :
    toMatrix F (append F x k v)
      = toMatrix F x + Matrix.vecMulVec (augValue v) (F.phi k) := by
  ext row r
  cases row with
  | inl u =>
      cases u
      simp [toMatrix, append, augValue, Matrix.vecMulVec_apply]
  | inr j =>
      simp [toMatrix, append, augValue, Matrix.vecMulVec_apply]

end State

/-- Softmax exponential kernel restricted to a finite declared query family. -/
noncomputable def softmaxFiniteFactorization
    {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
    (scale : ℝ) (Q : σ → κ → ℝ) : Factorization σ (κ → ℝ) σ where
  kernel := fun op k => Real.exp (scale * ∑ j, Q op j * k j)
  phi := fun k op => Real.exp (scale * ∑ j, Q op j * k j)
  psi := fun op r => if r = op then 1 else 0
  exact := by
    intro op k
    classical
    rw [Finset.sum_eq_single op]
    · simp
    · intro b hb hne
      simp [hne]
    · intro hop
      exact (hop (Finset.mem_univ op)).elim

/-- Linear coordinate dimension of the generic factorized recurrent state. -/
theorem state_finrank
    {Q K ρ ν : Type*} [Fintype ρ] [Fintype ν]
    (F : Factorization Q K ρ) :
    Module.finrank ℝ (State F ν) = Fintype.card ρ * (1 + Fintype.card ν) := by
  unfold State
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp [Finset.sum_const, Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Restricted kernel-function span over a declared query subset. -/
def restrictedKernelSpan {Q K : Type*}
    (kernel : Q → K → ℝ) (L : Set Q) : Submodule ℝ (K → ℝ) :=
  Submodule.span ℝ (kernel '' L)

/-- Richer legal query languages can only enlarge the restricted kernel span. -/
theorem restrictedKernelSpan_mono {Q K : Type*}
    (kernel : Q → K → ℝ) {L₁ L₂ : Set Q} (h : L₁ ⊆ L₂) :
    restrictedKernelSpan kernel L₁ ≤ restrictedKernelSpan kernel L₂ := by
  apply Submodule.span_mono
  exact Set.image_mono h

namespace Realization

open MemoryOperational

abbrev Item (K ν : Type*) := K × (ν → ℝ)

/-- Raw-cache machine for a factorized normalized kernel memory. -/
noncomputable def rawMachine {Q K ρ ν : Type*} [Fintype ρ]
    (F : Factorization Q K ρ) : Machine (List (Item K ν)) (Item K ν) (Q → ν → ℝ) where
  step cache item := item :: cache
  observe cache := fun q => State.rawRead F q cache

/-- The finite factorized state is an exact compiled realization of raw
normalized-kernel cache behavior under arbitrary matched future appends. -/
noncomputable def exactRealization {Q K ρ ν : Type*} [Fintype ρ]
    (F : Factorization Q K ρ) :
    MemoryOperational.Realization (rawMachine (ν := ν) F) (State F ν) where
  compile := State.compile F
  step := fun x item => State.append F x item.1 item.2
  observe := fun x q => State.read F x q
  step_commute := by
    intro cache item
    rfl
  observe_commute := by
    intro cache
    funext q j
    exact congrFun (State.read_compile_eq_rawRead F q cache).symm j

/-- Equality of compiled kernel states is a true right congruence for every
future append word, not merely equality of current reads. -/
theorem compiled_eq_implies_all_append_futures_equivalent
    {Q K ρ ν : Type*} [Fintype ρ]
    (F : Factorization Q K ρ)
    {xs ys : List (Item K ν)}
    (h : State.compile F xs = State.compile F ys) :
    (rawMachine (ν := ν) F).equivalent (fun _ => True) xs ys := by
  exact (exactRealization F).compile_eq_implies_equivalent (fun _ => True) h

end Realization

end KernelOperational
