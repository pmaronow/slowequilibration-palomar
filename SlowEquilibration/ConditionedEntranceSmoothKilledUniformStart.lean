-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledBounds
public import SlowEquilibration.SemigroupLaplaceRatePairing

/-! Exact physical Laplace killing transform averaged under the original
uniform sphere start. The Gibbs density is canceled exactly. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics SphericalReversibility
open SphericalForm
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def uniformDensity (D : SourceData N) (β : ℝ) (x : Vector N) : ℝ :=
  (gibbsDensity N β D.hamiltonian x)⁻¹

theorem uniformDensity_continuous (D : SourceData N) (β : ℝ) :
    Continuous (uniformDensity D β) :=
  (gibbsDensity_continuous β D.hamiltonian_contDiff.continuous).inv₀
    (fun x => (gibbsDensity_pos D.dimension_ge_one β D.hamiltonian_contDiff.continuous x).ne')

def uniformVector (D : SourceData N) (β : ℝ) : Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
    (uniformDensity D β) (uniformDensity_continuous D β)

theorem uniformDensity_integral_change (D : SourceData N) (β : ℝ) (f : Vector N → ℝ) :
    (∫ x,uniformDensity D β x*f x ∂gibbsLaw N β D.hamiltonian)=∫ x,f x ∂sphereLaw N := by
  rw [integral_gibbsLaw D.dimension_ge_one β D.hamiltonian_contDiff.continuous]
  apply integral_congr_ae
  exact .of_forall (fun x => by
    change gibbsDensity N β D.hamiltonian x *
      ((gibbsDensity N β D.hamiltonian x)⁻¹*f x)=f x
    rw [← mul_assoc,mul_inv_cancel₀
      (gibbsDensity_pos D.dimension_ge_one β D.hamiltonian_contDiff.continuous x).ne',one_mul])

theorem inner_uniformVector (D : SourceData N) (β : ℝ)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    inner ℝ U (uniformVector D β)=∫ x,U x ∂sphereLaw N := by
  rw [L2.inner_def,← uniformDensity_integral_change D β U]
  apply integral_congr_ae
  filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
    (uniformDensity D β) (uniformDensity_continuous D β)] with x hx
  change uniformVector D β x=uniformDensity D β x at hx
  simp only [RCLike.inner_apply,conj_trivial,hx]

theorem operator_killing_uniform_pairing (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) :
    inner ℝ (operator D β κ hκ hκ0 t (killingVector D β κ hκ)) (uniformVector D β)=
      ∫ x,expectation D β κ t κ x ∂sphereLaw N := by
  rw [L2.inner_def,← uniformDensity_integral_change D β (expectation D β κ t κ)]
  apply integral_congr_ae
  filter_upwards [operator_ae_expectation D β κ hκ hκ0 t (killingVector D β κ hκ) κ
    hκ.stronglyMeasurable (gibbsToL2_coe D.dimension_ge_one β D.hamiltonian
      D.hamiltonian_contDiff.continuous κ hκ),
    gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
      (uniformDensity D β) (uniformDensity_continuous D β)] with x hx hρ
  change uniformVector D β x=uniformDensity D β x at hρ
  simp only [RCLike.inner_apply,conj_trivial,hx,hρ]

/-- The averaged physical resolvent has the actual uniform initial law,
original time, true survival occupation and original Brownian law. -/
theorem rateLaplace_killing_uniform_integral (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (θ : ℝ≥0) (hθ : 0 < θ) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    (∫ x,h x ∂sphereLaw N)=
      ∫ t : ℝ in Ioi 0,Real.exp (-(θ : ℝ)*t)*
        (∫ x,expectation D β κ t.toNNReal κ x ∂sphereLaw N) := by
  dsimp only
  rw [← inner_uniformVector D β]
  change inner ℝ ((semigroupData D β κ hκ hκ0).rateOperator θ
    (killingVector D β κ hκ)) (uniformVector D β)=_
  rw [SemigroupLaplace.Data.inner_rateOperator_left (semigroupData D β κ hκ hκ0) θ hθ]
  apply integral_congr_ae
  exact .of_forall (fun t => congrArg (fun z => Real.exp (-(θ : ℝ)*t)*z)
    (operator_killing_uniform_pairing D β κ hκ hκ0 t.toNNReal))

end SlowEquilibration.ConditionedEntrance.SmoothKilled
