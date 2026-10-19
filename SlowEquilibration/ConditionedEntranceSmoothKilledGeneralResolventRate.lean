-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralResolventIdentification
public import SlowEquilibration.SemigroupLaplaceRate

/-! The genuine physical bounded-killing resolvent at every positive
Laplace rate, including the exponentially small source rate. Neither a
rate lower bound nor a resolvent identification is assumed. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalForm SphericalReversibility SphericalReversibility.Ito KilledOperator
open SphericalSmoothTensorStationarity FeynmanKac
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def rateLaplace (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (θ : ℝ≥0) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) →L[ℝ] Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  (semigroupData D β κ hκ hκ0).rateOperator θ

/-- This is the actual Brownian occupation-weighted semigroup integrated
in its original time variable at the literal physical rate θ. -/
theorem rateLaplace_integral (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (θ : ℝ≥0) (hθ : 0 < θ)
    (f : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    rateLaplace D β κ hκ hκ0 θ f =
      ∫ t : ℝ in Ioi 0, Real.exp (-(θ : ℝ)*t) •
        operator D β κ hκ hκ0 t.toNNReal f :=
  (semigroupData D β κ hκ hκ0).rateOperator_integral θ hθ f

theorem rateLaplace_identity (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) (x : (generator D β κ hκ K hK).domain) :
    rateLaplace D β κ hκ hκ0 θ
      ((θ : ℝ) • (x : Lp ℝ 2 (gibbsLaw N β D.hamiltonian))+
        generator D β κ hκ K hK x) = x := by
  apply SemigroupLaplace.Data.rateOperator_add_generator _ θ hθ _
    (generator_selfAdjoint D β κ hκ K hK).isClosed _
    (generator_C2_hasCore D β κ hκ K hK)
  rintro ⟨_,f,rfl⟩
  exact (generator_C2_physical_derivative D β κ hκ hκ0 K hK
    f (c2Functions_contDiff f)).choose_spec

def rateShiftedGenerator (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) (θ : ℝ≥0) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) →ₗ.[ℝ] Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  boundedPerturbation (generator D β κ hκ K hK)
    ((θ : ℝ) • ContinuousLinearMap.id ℝ _)

theorem rateShiftedGenerator_selfAdjoint (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) (θ : ℝ≥0) :
    IsSelfAdjoint (rateShiftedGenerator D β κ hκ K hK θ) := by
  apply boundedPerturbation_selfAdjoint _
    (generator_selfAdjoint D β κ hκ K hK)
  intro x y
  change inner ℝ ((θ : ℝ) • x) y=inner ℝ x ((θ : ℝ) • y)
  simp only [real_inner_smul_left,real_inner_smul_right]

theorem rateLaplace_leftInverse (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ)
    (x : (rateShiftedGenerator D β κ hκ K hK θ).domain) :
    rateLaplace D β κ hκ hκ0 θ
      (rateShiftedGenerator D β κ hκ K hK θ x)=x := by
  change rateLaplace D β κ hκ hκ0 θ
    (generator D β κ hκ K hK x+
      (θ : ℝ) • (x : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)))=x
  rw [add_comm]
  exact rateLaplace_identity D β κ hκ hκ0 K hK θ hθ x

theorem rateLaplace_mem_domain (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) (f : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    rateLaplace D β κ hκ hκ0 θ f ∈
      (generator D β κ hκ K hK).domain :=
  leftInverse_domain _ (rateShiftedGenerator_selfAdjoint D β κ hκ K hK θ) _
    (rateLaplace_leftInverse D β κ hκ hκ0 K hK θ hθ) f

/-- Exact physical two-sided inverse of `θ+A+κ` for every θ>0. -/
theorem rateLaplace_resolvent (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) (f : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    (θ : ℝ) • rateLaplace D β κ hκ hκ0 θ f+
      generator D β κ hκ K hK
        ⟨rateLaplace D β κ hκ hκ0 θ f,
          rateLaplace_mem_domain D β κ hκ hκ0 K hK θ hθ f⟩=f := by
  have h := leftInverse_rightInverse _
    (rateShiftedGenerator_selfAdjoint D β κ hκ K hK θ) _
    (rateLaplace_leftInverse D β κ hκ hκ0 K hK θ hθ) f
  change generator D β κ hκ K hK
    ⟨rateLaplace D β κ hκ hκ0 θ f,_⟩+
      (θ : ℝ) • rateLaplace D β κ hκ hκ0 θ f=f at h
  exact (add_comm _ _).trans h

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
