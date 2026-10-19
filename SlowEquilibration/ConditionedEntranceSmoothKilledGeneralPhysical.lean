-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralField

/-! Genuine killed Brownian kernel and Gibbs L² contraction for any smooth
Hamiltonian with proved finite-tensor approximation, including the actual
proper-pure posterior cutoff. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalAging HardSphereDynamics
open SphericalSmoothTensorStationarity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def kernel (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ)
    (t : ℝ≥0) : Kernel (Vector N) (Vector N) :=
  FeynmanKac.killedKernel
    (SphericalC1Dynamics.cutoffDrift_lipschitz β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff)
      (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec κ hκ t

theorem kernel_finite (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) : IsFiniteKernel (kernel D β κ hκ t) :=
  FeynmanKac.killedKernel_finite _ _ κ hκ hκ0 t

theorem kernel_le_original (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) (x : Vector N) :
    kernel D β κ hκ t x ≤ D.transitionKernel β t x :=
  FeynmanKac.killedLaw_le_original _ _ κ hκ hκ0 t x

theorem kernel_mass_le (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) (x : Vector N) :
    kernel D β κ hκ t x univ ≤ 1 :=
  (kernel_le_original D β κ hκ hκ0 t x univ).trans_eq (by simp)

theorem kernel_add (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (s t : ℝ≥0) (x : Vector N) :
    kernel D β κ hκ (s+t) x=(kernel D β κ hκ t ∘ₖ kernel D β κ hκ s) x :=
  FeynmanKac.killedKernel_add _ _
    (SphericalC1Dynamics.coefficientBounds β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff)) κ hκ hκ0 s t x

theorem kernel_gibbs_subinvariant (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) :
    kernel D β κ hκ t ∘ₘ gibbsLaw N β D.hamiltonian ≤ gibbsLaw N β D.hamiltonian := by
  have he : kernel D β κ hκ t ∘ₘ gibbsLaw N β D.hamiltonian ≤
      D.transitionKernel β t ∘ₘ gibbsLaw N β D.hamiltonian := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.bind_apply hA (Kernel.aemeasurable _),Measure.bind_apply hA (Kernel.aemeasurable _)]
    exact lintegral_mono (fun x => kernel_le_original D β κ hκ hκ0 t x A)
  exact he.trans_eq (D.stationary β t)

def operator (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) →L[ℝ] Lp ℝ 2 (gibbsLaw N β D.hamiltonian) := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let := kernel_finite D β κ hκ hκ0 t
  exact KilledL2.operator _ (kernel D β κ hκ t) (kernel_mass_le D β κ hκ hκ0 t)
    (kernel_gibbs_subinvariant D β κ hκ hκ0 t)

theorem operator_norm_le (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) :
    ‖operator D β κ hκ hκ0 t‖ ≤ 1 := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let := kernel_finite D β κ hκ hκ0 t
  exact KilledL2.operator_norm_le _ _ _ _

theorem operator_ae (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    operator D β κ hκ hκ0 t U =ᵐ[gibbsLaw N β D.hamiltonian]
      fun x => ∫ y,U y ∂kernel D β κ hκ t x := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let := kernel_finite D β κ hκ hκ0 t
  exact KilledL2.operator_ae _ _ _ _ U

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
