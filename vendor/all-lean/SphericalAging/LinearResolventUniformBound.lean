module

public import SphericalAging.LinearResolvent

public section
/-! A common bound for all genuine bounded-Jacobian source resolvents. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.LinearResolventUniformBound
open HardSphereDynamics LocalSDE LinearVariationalSDE PredictableLinearCoefficient WeightedPredictable
open PredictableItoTime PredictableDriftTime
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
theorem sourceClass_uniform_lipschitz (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (T : ℝ≥0) : ∃ K : ℝ≥0, ∀ (hb : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
      (hs : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks), LipschitzWith K (sourceClass D hb hs T) := by
  obtain ⟨α, hα, Cd, Ci, hCd, hCi, hsmall⟩ := WeightedPicard.exists_contraction_parameters N Kb Ks T
  have hd : ∀ V : PredictableProcessL2 F P, ‖multiply α T (driftVolterra T V)‖ ≤ Cd * ‖multiply α T V‖ := by
    intro V
    rw [hCd]
    exact WeightedDriftNorm.norm_weighted_driftVolterra_le hα T V
  have hi : ∀ j (V : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T V)‖ ≤
        Ci * ‖multiply α T V‖ := by
    intro j V
    rw [hCi, one_div]
    exact WeightedItoNorm.norm_weighted_itoVolterra_le (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) hα T V
  let q : ℝ := (N : ℝ)*Cd*Kb + (N : ℝ)^2*Ci*Ks
  have hq : q < 1 := by dsimp only [q]; exact_mod_cast hsmall
  let C : ℝ := Real.exp (|α| * T) * Real.exp (|α| * T) / (1-q)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨⟨C, hC⟩,?_⟩
  intro hb hs
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simp only [dist_eq_norm]
  have hw := weighted_sourceClass_sub_bound D hb hs α T Cd Ci hd hi hsmall A B
  have hu : sourceClass D hb hs T A - sourceClass D hb hs T B =
      multiply (-α) T (multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B)) :=
    (inverse_multiply α T _).symm
  calc
    _ = ‖multiply (-α) T (multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B))‖ := congrArg norm hu
    _ ≤ Real.exp (|α| * T) * ‖multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B)‖ := by
      simpa only [abs_neg] using norm_multiply_le (-α) T (multiply α T (sourceClass D hb hs T A - sourceClass D hb hs T B))
    _ ≤ Real.exp (|α| * T) * (‖multiply α T (A-B)‖ / (1-q)) := mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ ≤ Real.exp (|α| * T) * ((Real.exp (|α| * T) * ‖A-B‖) / (1-q)) :=
      mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right (sub_pos.mpr hq)).mpr (norm_multiply_le α T (A-B))) (Real.exp_pos _).le
    _ = C * ‖A-B‖ := by dsimp only [C]; ring

theorem sourceLinearMap_uniform_norm (D : BrownianDriver N P F) (Kb Ks T : ℝ≥0) :
    ∃ C : ℝ,0≤C ∧ ∀ (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
      (s : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks),
      ‖LinearResolvent.sourceLinearMap D a s T‖≤C := by
  obtain ⟨K,hK⟩ := sourceClass_uniform_lipschitz (Kb := Kb) (Ks := Ks) D T
  refine ⟨K,K.coe_nonneg,?_⟩
  intro a s
  exact ContinuousLinearMap.opNorm_le_of_lipschitz (hK a s)
end SphericalAging.LinearResolventUniformBound
