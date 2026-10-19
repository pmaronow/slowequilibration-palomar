module

public import SphericalAging.RandomVectorSDEEighthLocalization
public import SphericalAging.LinearSDETimeFourthMoment
public import SphericalAging.RandomLinearSDETimeFourthMoment

public section

/-! Actual product-time eighth moments for full-filtration bounded matrix
SDEs with bounded correlated random initial data. The moment rate uses
the vector drift and whole matrix trace, both derived from coefficient
operator bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.RandomLinearSDETimeEighthMoment
open HardSphereDynamics LocalSDE PredictableLinearCoefficient
open LinearSDETimeFourthMoment RandomVectorSDEEighthLocalization RandomLinearSDETimeFourthMoment
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1400000

@[expose] def momentRate (N : ℕ) (Kb Ks : ℝ≥0) : ℝ≥0 := 8*(N*Kb)+4+28*(N^2*Ks^2)

@[expose] def momentConstant (N : ℕ) (Kb Ks T : ℝ≥0) (Z0 : Ω → State N) (P : Measure Ω) : ℝ :=
  (∫ omega,‖Z0 omega‖^8 ∂P)*Real.exp ((momentRate N Kb Ks : ℝ)*T)

lemma momentConstant_nonneg (Kb Ks T : ℝ≥0) (Z0 : Ω → State N) :
    0 ≤ RandomLinearSDETimeEighthMoment.momentConstant N Kb Ks T Z0 P := by unfold momentConstant;positivity

theorem linear_solution_eighthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D Z0 X T)
    (hm : MemLp Z0 8 P) (R0 : ℝ≥0) (hbound : ∀ᵐ omega ∂P,‖Z0 omega‖ ≤ R0)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) :
    MemLp (X t) 8 P ∧ (∫ omega,‖X t omega‖^8 ∂P) ≤ RandomLinearSDETimeEighthMoment.momentConstant N Kb Ks T Z0 P := by
  have hh := random_vector_solution_eighthMoment h hm R0 hbound (N*Kb) (N^2*Ks^2)
    (coefficient_driftNorm a) (coefficient_noiseTrace sigma) hnull t ht
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (integral_nonneg (fun _ => by positivity))
  exact mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ T from ht) (momentRate N Kb Ks).coe_nonneg

/-- Actual product-time L⁸ integrability and its explicit eighth bound,
proved from the genuine random-initial matrix SDE and coefficient bounds. -/
theorem linear_solution_time_eighthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D Z0 X T)
    (hm : MemLp Z0 8 P) (R0 : ℝ≥0) (hbound : ∀ᵐ omega ∂P,‖Z0 omega‖ ≤ R0)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    MemLp (stateTimeCut X T) 8 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut X T q‖^8 ∂nonnegativeLebesgueMeasure.prod P) ≤
        (T : ℝ)*RandomLinearSDETimeEighthMoment.momentConstant N Kb Ks T Z0 P := by
  let μ := nonnegativeLebesgueMeasure
  letI : IsFiniteMeasure (μ.restrict (Ioc (0 : ℝ≥0) T)) := by
    change IsFiniteMeasure (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
    infer_instance
  let H : ℝ≥0 × Ω → ℝ := fun q => ‖stateTimeCut X T q‖^8
  let C := RandomLinearSDETimeEighthMoment.momentConstant N Kb Ks T Z0 P
  have hC : 0 ≤ C := momentConstant_nonneg Kb Ks T Z0
  have hsm := stateTimeCut_aestronglyMeasurable X h.1 h.2.1 T
  have hHsm : AEStronglyMeasurable H (μ.prod P) := hsm.norm.pow 8
  have hHi (s : ℝ≥0) : Integrable (fun ω => H (s,ω)) P := by
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) T
    · have hm := (linear_solution_eighthMoment h hm R0 hbound hnull s hs.2).1
      have hh := hm.integrable_norm_rpow'
      simpa only [H,stateTimeCut,hs,ite_true,ENNReal.toReal_ofNat,Real.rpow_ofNat] using hh
    · simp only [H,stateTimeCut,hs,ite_false,norm_zero,zero_pow (by norm_num : 8 ≠ 0)]
      simp
  let g : ℝ≥0 → ℝ := fun s => ∫ ω,‖H (s,ω)‖ ∂P
  have hgsm : AEStronglyMeasurable g μ := hHsm.norm.integral_prod_right'
  have hgpos (s : ℝ≥0) : 0 ≤ g s := integral_nonneg (fun _ => norm_nonneg _)
  have hg_bound (s : ℝ≥0) (hs : s ∈ Ioc (0 : ℝ≥0) T) : ‖g s‖ ≤ C := by
    rw [Real.norm_of_nonneg (hgpos s)]
    have he : g s=(∫ ω,‖X s ω‖^8 ∂P) := by
      apply integral_congr_ae
      exact .of_forall (fun ω => by
        dsimp [g,H,stateTimeCut]
        rw [ite_eq_left hs,abs_of_nonneg (by positivity)])
    rw [he]
    exact (linear_solution_eighthMoment h hm R0 hbound hnull s hs.2).2
  have hg_on : IntegrableOn g (Ioc (0 : ℝ≥0) T) μ := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound hgsm.restrict C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hg_bound s hs
  have hg_zero (s : ℝ≥0) (hs : s ∉ Ioc (0 : ℝ≥0) T) : g s=0 := by
    dsimp only [g,H,stateTimeCut]
    simp only [hs,ite_false,norm_zero,zero_pow (by norm_num : 8 ≠ 0)]
    simp
  have hgi : Integrable g μ := by
    have hi := hg_on.integrable_indicator measurableSet_Ioc
    convert hi using 1
    funext s
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) T
    · simp [hs]
    · simp [hs,hg_zero s hs]
  have hHi_prod : Integrable H (μ.prod P) :=
    (integrable_prod_iff hHsm).mpr ⟨.of_forall hHi,hgi⟩
  have hm : MemLp (stateTimeCut X T) 8 (μ.prod P) := by
    apply (integrable_norm_rpow_iff hsm (by norm_num : (8 : ℝ≥0∞) ≠ 0)
      (by norm_num : (8 : ℝ≥0∞) ≠ ∞)).mp
    simpa only [H,ENNReal.toReal_ofNat,Real.rpow_ofNat] using hHi_prod
  refine ⟨hm,?_⟩
  have he : (∫ q,H q ∂μ.prod P)=∫ s,g s ∂μ := by
    rw [integral_prod _ hHi_prod]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      apply integral_congr_ae
      exact .of_forall (fun ω => by dsimp [g,H];rw [abs_of_nonneg (by positivity)]))
  rw [show (∫ q,‖stateTimeCut X T q‖^8 ∂μ.prod P)=∫ s,g s ∂μ from he]
  calc
    _ = ∫ s in Ioc (0 : ℝ≥0) T,g s ∂μ := by
      rw [← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact .of_forall (fun s => by by_cases hs : s ∈ Ioc (0 : ℝ≥0) T <;> simp [hs,hg_zero s])
    _ ≤ ∫ s in Ioc (0 : ℝ≥0) T,C ∂μ := by
      apply integral_mono_ae hg_on (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (le_abs_self (g s)).trans (hg_bound s hs)
    _ = (T : ℝ)*C := by
      simp [μ,Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal T.coe_nonneg]

end SphericalAging.RandomLinearSDETimeEighthMoment
