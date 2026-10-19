module

public import SphericalAging.FlowCoefficientApplicationContinuity

public section
/-! Joint continuity of genuine coefficient evaluation in state and data. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowCoefficientJointApplicationContinuity
open HardSphereDynamics LocalSDE PredictableLinearCoefficient SecondVariationSourceError
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 512
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem apply_row_joint_continuous (D : BrownianDriver N P F) {Kb Ks K L : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g)) :
    Continuous (fun z : State N × PredictableStateL2 N F P => apply (row D hb hs T g hg hK z.1) z.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' (K := K)
  · intro x
    apply LipschitzWith.of_dist_le_mul
    intro U V
    rw [dist_eq_norm,dist_eq_norm,←apply_sub]
    exact norm_apply_le (row D hb hs T g hg hK x) (U-V)
  · intro Q
    exact FlowCoefficientApplicationContinuity.apply_row_continuous D hb hs T g hg hK hL Q

theorem apply_row_of_continuous (D : BrownianDriver N P F) {Kb Ks K L : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (Q : State N → PredictableStateL2 N F P) (hQ : Continuous Q) :
    Continuous (fun x => apply (row D hb hs T g hg hK x) (Q x)) :=
by
  have hc := apply_row_joint_continuous D hb hs T g hg hK hL
  have hp : Continuous (fun x : State N => (x,Q x)) := continuous_id.prodMk hQ
  have hr := hc.comp hp
  exact hr.congr (fun x => rfl)
end SphericalAging.FlowCoefficientJointApplicationContinuity
