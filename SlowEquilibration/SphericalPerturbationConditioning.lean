-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalUnitSpinTransport

/-! Actual conditioning of independent Gaussian field banks into the
ordinary Gibbs spin law, followed by the genuine tensor positivity bank.
The normalized law identity is derived from Gibbs densities and radial
transport, not supplied as a conditional model premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology RealInnerProductSpace

set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual tensor field evaluated on radial unit spins. -/
def radialPerturbation {N K : ℕ} (a : Fin K → ℝ) (r : ℝ)
    (x : Vector N) : PerturbationDisorder N K →L[ℝ] ℝ := linear a (scaleToUnit r x)

theorem radialPerturbation_measurable {N K : ℕ} (a : Fin K → ℝ) (r : ℝ) :
    Measurable (radialPerturbation (N := N) a r) :=
  (linear_measurable a).comp (scaleToUnit_measurable N r)

/-- Pullback to the true unit-spin subtype is literally the tensor feature
used in the quantitative positivity theorem. -/
theorem radialPerturbation_fromUnit {N K : ℕ} (a : Fin K → ℝ) {r : ℝ} (hr : r≠0)
    (z : UnitSpin N) : radialPerturbation a r (fromUnit r z)=unitLinear a z := by
  simp only [radialPerturbation,scaleToUnit,fromUnit,smul_smul,inv_mul_cancel₀ hr,one_smul,unitLinear]

/-- Conditioning any bounded measurable Gaussian base field on an actual
spherical spin law yields a genuine probability measure on UnitSpin. -/
theorem conditioned_unitLaw_probability {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0<r)
    (hμ : ∀ᵐ x ∂μ,‖x‖=r) (L : Vector N → H →L[ℝ] ℝ) (hL : Measurable L)
    {B : ℝ} (hb : ∀ᵐ x ∂μ,‖L x‖≤B) (w : H) :
    IsProbabilityMeasure (unitLaw (gibbsMeasure μ L w) r) := by
  let _ := gibbsMeasure_probability μ L hL hb w
  apply unitLaw_probability _ hr
  exact (gibbsMeasure_absolutelyContinuous μ L w).ae_le hμ

/-- Exact original-law identification after conditioning the first bank.
The true combined field splits into the base bank and radial tensor bank;
all partition ratios, density products and radius normalizations are
proved by the preceding ordinary Gibbs and sphere transport lemmas. -/
theorem gibbsMeasure_radial_bank_split {N K : ℕ} {H HT : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup HT] [NormedSpace ℝ HT] [CompleteSpace HT] [FiniteDimensional ℝ HT]
    (μ : Measure (Vector N)) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0<r)
    (hμ : ∀ᵐ x ∂μ,‖x‖=r) (L : Vector N → H →L[ℝ] ℝ) (hL : Measurable L)
    {B : ℝ} (hb : ∀ᵐ x ∂μ,‖L x‖≤B) (w : H)
    (a : Fin K → ℝ) (z : PerturbationDisorder N K)
    (T : Vector N → HT →L[ℝ] ℝ) (hT : Measurable T) {BT : ℝ}
    (hbT : ∀ᵐ x ∂μ,‖T x‖≤BT) (u : HT)
    (hsplit : ∀ᵐ x ∂μ,T x u=L x w+radialPerturbation a r x z) :
    gibbsMeasure μ T u=
      (gibbsMeasure (unitLaw (gibbsMeasure μ L w) r) (unitLinear a) z).map (fromUnit r) := by
  have hM := radialPerturbation_measurable (N := N) a r
  have hG : ∀ᵐ x ∂gibbsMeasure μ L w,‖x‖=r :=
    (gibbsMeasure_absolutelyContinuous μ L w).ae_le hμ
  calc
    _=gibbsMeasure (gibbsMeasure μ L w) (radialPerturbation a r) z :=
      (gibbsMeasure_associate μ L hL hb w (radialPerturbation a r) hM z T hT hbT u hsplit).symm
    _=(gibbsMeasure (unitLaw (gibbsMeasure μ L w) r)
        (fun x => radialPerturbation a r (fromUnit r x)) z).map (fromUnit r) :=
      (unitLaw_gibbs_map _ hr hG (radialPerturbation a r) hM z).symm
    _=_ := by
      congr 1
      apply gibbsMeasure_congr_field
      exact .of_forall fun x => congrArg (fun f => f z) (radialPerturbation_fromUnit a hr.ne' x)

end SlowEquilibration.SphericalPositivePerturbation
