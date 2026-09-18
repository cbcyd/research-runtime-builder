import OfflineBundle.BundleImports

namespace MemoryOperational

/-- A legal future language is a predicate on finite operation words. -/
abbrev Language (U : Type*) := List U → Prop

/-- Deterministic state machine with an explicit observer. -/
structure Machine (X U Y : Type*) where
  step : X → U → X
  observe : X → Y

namespace Machine

variable {X U Y : Type*} (M : Machine X U Y)

/-- Execute a chronological word of future operations. -/
def run : X → List U → X
  | x, [] => x
  | x, u :: us => run (M.step x u) us

@[simp] theorem run_nil (x : X) : M.run x [] = x := rfl

@[simp] theorem run_cons (x : X) (u : U) (us : List U) :
    M.run x (u :: us) = M.run (M.step x u) us := rfl

/-- Two physical states are operationally equivalent relative to a declared
future language when every legal future word produces the same observation. -/
def equivalent (L : Language U) (x y : X) : Prop :=
  ∀ w, L w → M.observe (M.run x w) = M.observe (M.run y w)

@[refl] theorem equivalent_refl (L : Language U) (x : X) :
    M.equivalent L x x := by
  intro w hw
  rfl

@[symm] theorem equivalent_symm (L : Language U) {x y : X}
    (h : M.equivalent L x y) : M.equivalent L y x := by
  intro w hw
  exact (h w hw).symm

@[trans] theorem equivalent_trans (L : Language U) {x y z : X}
    (hxy : M.equivalent L x y) (hyz : M.equivalent L y z) :
    M.equivalent L x z := by
  intro w hw
  exact (hxy w hw).trans (hyz w hw)

/-- Operational equivalence is an actual equivalence relation for every fixed
future language. -/
def operationalSetoid (L : Language U) : Setoid X where
  r := M.equivalent L
  iseqv := ⟨M.equivalent_refl L, M.equivalent_symm L, M.equivalent_trans L⟩

/-- Restrict a language after committing to one next operation. -/
def derivative (L : Language U) (u : U) : Language U :=
  fun w => L (u :: w)

/-- Exact derivative-language congruence. No closure assumption is needed:
after executing `u`, the legal suffix language is the derivative of `L`. -/
theorem equivalent_after_step_derivative
    (L : Language U) {x y : X} (u : U)
    (h : M.equivalent L x y) :
    M.equivalent (derivative L u) (M.step x u) (M.step y u) := by
  intro w hw
  exact h (u :: w) hw

/-- If a language is closed under prepending one operation, its operational
quotient is a genuine right congruence for that operation. -/
theorem equivalent_after_step_of_prepend_closed
    (L : Language U) {x y : X} (u : U)
    (hclosed : ∀ w, L w → L (u :: w))
    (h : M.equivalent L x y) :
    M.equivalent L (M.step x u) (M.step y u) := by
  intro w hw
  exact h (u :: w) (hclosed w hw)

/-- Enlarging the future language can only refine the operational quotient. -/
theorem equivalent_mono
    {L₁ L₂ : Language U}
    (hsub : ∀ w, L₁ w → L₂ w) {x y : X}
    (h : M.equivalent L₂ x y) : M.equivalent L₁ x y := by
  intro w hw
  exact h w (hsub w hw)

/-- Horizon-bounded future language. -/
def horizonLanguage (H : ℕ) : Language U :=
  fun w => w.length ≤ H

/-- Increasing horizon refines the quotient monotonically. -/
theorem equivalent_horizon_mono {H₁ H₂ : ℕ} (hH : H₁ ≤ H₂)
    {x y : X} (h : M.equivalent (horizonLanguage H₂) x y) :
    M.equivalent (horizonLanguage H₁) x y := by
  apply M.equivalent_mono (L₁ := horizonLanguage H₁)
    (L₂ := horizonLanguage H₂)
  · intro w hw
    exact le_trans hw hH
  · exact h

/-- An H+1 equivalence before one operation yields H equivalence after it. -/
theorem equivalent_horizon_after_step {H : ℕ} {x y : X} (u : U)
    (h : M.equivalent (horizonLanguage (H + 1)) x y) :
    M.equivalent (horizonLanguage H) (M.step x u) (M.step y u) := by
  intro w hw
  apply h (u :: w)
  change w.length ≤ H at hw
  change w.length + 1 ≤ H + 1
  exact Nat.add_le_add_right hw 1

/-- Language containing only the empty future. -/
def currentLanguage : Language U := fun w => w = []

/-- Current-observer equivalence is exactly operational equivalence for the
zero-horizon language; it need not be stable under any nonempty future. -/
theorem equivalent_current_iff {x y : X} :
    M.equivalent (currentLanguage : Language U) x y ↔ M.observe x = M.observe y := by
  constructor
  · intro h
    simpa using h [] rfl
  · intro h w hw
    change w = [] at hw
    subst w
    simpa using h

end Machine

/-- Exact compiled realization of one deterministic machine by another state
space with the same operation alphabet and output type. -/
structure Realization {X U Y : Type*} (M : Machine X U Y) (Z : Type*) where
  compile : X → Z
  step : Z → U → Z
  observe : Z → Y
  step_commute : ∀ x u, compile (M.step x u) = step (compile x) u
  observe_commute : ∀ x, M.observe x = observe (compile x)

namespace Realization

variable {X U Y Z : Type*} {M : Machine X U Y} (R : Realization M Z)

/-- Execute a word in the realized state space. -/
def run : Z → List U → Z
  | z, [] => z
  | z, u :: us => run (R.step z u) us

/-- Compilation commutes with every finite future word. -/
theorem compile_run (x : X) (w : List U) :
    R.compile (M.run x w) = R.run (R.compile x) w := by
  induction w generalizing x with
  | nil => rfl
  | cons u us ih =>
      rw [Machine.run_cons, ih]
      rw [R.step_commute]
      rfl

/-- Equality of compiled states is sufficient for exact behavioral equivalence
under every declared future language. -/
theorem compile_eq_implies_equivalent
    (L : Language U) {x y : X} (h : R.compile x = R.compile y) :
    M.equivalent L x y := by
  intro w hw
  rw [R.observe_commute, R.observe_commute]
  rw [R.compile_run, R.compile_run, h]

/-- A realization is separating for a language if behavioral equivalence can
be recovered from its state equality. -/
def Separating (L : Language U) : Prop :=
  ∀ x y, M.equivalent L x y → R.compile x = R.compile y

/-- A separating exact realization identifies precisely the operational
quotient classes of its declared future language. -/
theorem compile_eq_iff_equivalent
    (L : Language U) (hsep : R.Separating L) (x y : X) :
    R.compile x = R.compile y ↔ M.equivalent L x y := by
  constructor
  · exact R.compile_eq_implies_equivalent L
  · exact hsep x y

end Realization

end MemoryOperational
