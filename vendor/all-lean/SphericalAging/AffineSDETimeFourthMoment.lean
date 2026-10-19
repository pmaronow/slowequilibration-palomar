module

public import SphericalAging.AffineSDELocalization
public import SphericalAging.LinearSDETimeFourthMoment

public section

/-! Actual product-time fourth moments for bounded predictable affine
stochastic equations, including the zero-initial disorder response. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AffineSDETimeFourthMoment
open HardSphereDynamics InhomogeneousLinearSDE PredictableLinearCoefficient
  LinearSDEFourthMoment AffineSDEFourthMoment AffineSDELocalization
  LinearSDETimeFourthMoment
set_option maxHeartbeats 1200000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
@[expose] def momentExponent (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  3*(T : ℝ)*(affineRadialDriftConstant N Kb Ks : ℝ)^2+3*N*(radialNoiseConstant N Ks : ℝ)^2

@[expose] def momentConstant (N : ℕ) (Kb Ks B T : ℝ≥0) (v0 : State N) : ℝ :=
  3*((B : ℝ)^2+‖v0‖^2)^2*Real.exp (momentExponent N Kb Ks T*T)

theorem momentExponent_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) : 0 ≤ momentExponent N Kb Ks T := by
  unfold momentExponent
  positivity

theorem momentConstant_nonneg (N : ℕ) (Kb Ks B T : ℝ≥0) (v0 : State N) :
    0 ≤ momentConstant N Kb Ks B T v0 := by unfold momentConstant;positivity

/-- Uniform fourth-moment bound on every time in the actual horizon. -/
theorem affine_solution_fourthMoment_uniform {Kb Ks B : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) : (∫ ω,‖X t ω‖^4 ∂P) ≤ momentConstant N Kb Ks B T v0 := by
  have hh := (affine_solution_fourthMoment h hnull t ht).2
  refine hh.trans ?_
  unfold momentConstant momentExponent
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ T from ht) (momentExponent_nonneg N Kb Ks T))) (by positivity)

/-- The genuine finite-horizon state has an actual product-time L⁴ class.
Its fourth moment is bounded by the horizon times the explicit uniform
pointwise fourth-moment constant. -/
theorem affine_solution_time_fourthMoment {Kb Ks B : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    MemLp (stateTimeCut X T) 4 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut X T q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤
        (T : ℝ)*momentConstant N Kb Ks B T v0 := by
  let μ := nonnegativeLebesgueMeasure
  letI : IsFiniteMeasure (μ.restrict (Ioc (0 : ℝ≥0) T)) := by
    change IsFiniteMeasure (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
    infer_instance
  let H : ℝ≥0 × Ω → ℝ := fun q => ‖stateTimeCut X T q‖^4
  let C := momentConstant N Kb Ks B T v0
  have hC : 0 ≤ C := momentConstant_nonneg N Kb Ks B T v0
  have hsm := stateTimeCut_aestronglyMeasurable X h.1 h.2.1 T
  have hHsm : AEStronglyMeasurable H (μ.prod P) := hsm.norm.pow 4
  have hHi (s : ℝ≥0) : Integrable (fun ω => H (s,ω)) P := by
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) T
    · have hm := (affine_solution_fourthMoment h hnull s hs.2).1
      have hh := hm.integrable_norm_rpow'
      simpa only [H,stateTimeCut,hs,ite_true,ENNReal.toReal_ofNat,Real.rpow_ofNat] using hh
    · simp only [H,stateTimeCut,hs,ite_false,norm_zero,zero_pow (by norm_num : 4 ≠ 0)]
      simp
  let g : ℝ≥0 → ℝ := fun s => ∫ ω,‖H (s,ω)‖ ∂P
  have hgsm : AEStronglyMeasurable g μ := hHsm.norm.integral_prod_right'
  have hgpos (s : ℝ≥0) : 0 ≤ g s := integral_nonneg (fun _ => norm_nonneg _)
  have hg_bound (s : ℝ≥0) (hs : s ∈ Ioc (0 : ℝ≥0) T) : ‖g s‖ ≤ C := by
    rw [Real.norm_of_nonneg (hgpos s)]
    have he : g s=(∫ ω,‖X s ω‖^4 ∂P) := by
      apply integral_congr_ae
      exact .of_forall (fun ω => by
        dsimp [g,H,stateTimeCut]
        rw [ite_eq_left hs,abs_of_nonneg (by positivity)])
    rw [he]
    exact affine_solution_fourthMoment_uniform h hnull s hs.2
  have hg_on : IntegrableOn g (Ioc (0 : ℝ≥0) T) μ := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound hgsm.restrict C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hg_bound s hs
  have hg_zero (s : ℝ≥0) (hs : s ∉ Ioc (0 : ℝ≥0) T) : g s=0 := by
    dsimp only [g,H,stateTimeCut]
    simp only [hs,ite_false,norm_zero,zero_pow (by norm_num : 4 ≠ 0)]
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
  have hm : MemLp (stateTimeCut X T) 4 (μ.prod P) := by
    apply (integrable_norm_rpow_iff hsm (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
    simpa only [H,ENNReal.toReal_ofNat,Real.rpow_ofNat] using hHi_prod
  refine ⟨hm,?_⟩
  have he : (∫ q,H q ∂μ.prod P)=∫ s,g s ∂μ := by
    rw [integral_prod _ hHi_prod]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      apply integral_congr_ae
      exact .of_forall (fun ω => by dsimp [g,H];rw [abs_of_nonneg (by positivity)]))
  rw [show (∫ q,‖stateTimeCut X T q‖^4 ∂μ.prod P)=∫ s,g s ∂μ from he]
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

theorem affine_solution_time_fourthMoment_augmented {Kb Ks B : ℝ≥0}
    (F₀ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {a : Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Ks}
    {forcing : Fin N → Forcing (F := NullAugmentation.augment F₀ P) (P := P) B}
    {D : BrownianDriver N P (NullAugmentation.augment F₀ P)} {v0 : State N}
    {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T) :
    MemLp (stateTimeCut X T) 4 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut X T q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤
        (T : ℝ)*momentConstant N Kb Ks B T v0 :=
  affine_solution_time_fourthMoment h
    (fun _ hm hzero => NullAugmentation.augment_null_known_zero F₀ hm hzero)

/-- Zero-initial forcing has a genuinely quartic moment bound. -/
theorem momentConstant_zero (N : ℕ) (Kb Ks B T : ℝ≥0) :
    momentConstant N Kb Ks B T 0 =
      3*(B : ℝ)^4*Real.exp (momentExponent N Kb Ks T*T) := by
  simp only [momentConstant,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero]
  ring

/-- Both initial data and forcing scale quartically. -/
theorem momentConstant_scale (N : ℕ) (Kb Ks B T b : ℝ≥0) (v0 : State N) :
    momentConstant N Kb Ks (b*B) T ((b : ℝ) • v0) =
      (b : ℝ)^4*momentConstant N Kb Ks B T v0 := by
  simp only [momentConstant,NNReal.coe_mul,norm_smul,Real.norm_of_nonneg b.coe_nonneg]
  ring

end SphericalAging.AffineSDETimeFourthMoment
