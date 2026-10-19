module

public import SphericalAging.LinearSDELocalization

public section

/-! Actual fourth moments on the time–probability product, used for
Taylor remainders in the predictable L² norm. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.LinearSDETimeFourthMoment
open HardSphereDynamics LinearVariationalSDE PredictableLinearCoefficient
  LinearSDEFourthMoment LinearSDELocalization
set_option maxHeartbeats 1200000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def stateTimeCut (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) (q : ℝ≥0 × Ω) : State N :=
  if q.1 ∈ Ioc (0 : ℝ≥0) T then X q.1 q.2 else 0

theorem stateTimeCut_aestronglyMeasurable (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω)) (T : ℝ≥0) :
    AEStronglyMeasurable (stateTimeCut X T) (nonnegativeLebesgueMeasure.prod P) := by
  have hi (i : Fin N) : AEStronglyMeasurable
      (FourPapersCommon.continuousAdaptedTimeCut (fun s ω => X s ω i) T)
      (nonnegativeLebesgueMeasure.prod P) := by
    have hp : AEStronglyMeasurable[F.predictable]
        (FourPapersCommon.continuousAdaptedTimeCut (fun s ω => X s ω i) T)
        (nonnegativeLebesgueMeasure.prod P) := by
      apply FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F
      · exact SpherePreservation.coordinates_adapted hXa i
      · filter_upwards [hXc] with ω hω
        exact (CutoffSDE.coordinate_lipschitz i).continuous.comp hω
    exact hp.mono (predictable_le_prod F)
  have hs := Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => (hi i).smul_const (basisVector i))
  convert hs using 1
  funext q
  by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [stateTimeCut,hq,ite_true,FourPapersCommon.continuousAdaptedTimeCut]
    exact (LocalSDE.state_sum_basis (X q.1 q.2)).symm
  · simp [stateTimeCut,hq,FourPapersCommon.continuousAdaptedTimeCut]

@[expose] def momentExponent (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  3*(T : ℝ)*(radialDriftConstant N Kb Ks : ℝ)^2+3*N*(radialNoiseConstant N Ks : ℝ)^2

@[expose] def momentConstant (N : ℕ) (Kb Ks T : ℝ≥0) (v0 : State N) : ℝ :=
  3*‖v0‖^4*Real.exp (momentExponent N Kb Ks T*T)

theorem momentExponent_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) : 0 ≤ momentExponent N Kb Ks T := by
  unfold momentExponent
  positivity

theorem momentConstant_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) (v0 : State N) :
    0 ≤ momentConstant N Kb Ks T v0 := by unfold momentConstant;positivity

/-- Uniform fourth-moment bound on every time in the actual horizon. -/
theorem linear_solution_fourthMoment_uniform {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) : (∫ ω,‖X t ω‖^4 ∂P) ≤ momentConstant N Kb Ks T v0 := by
  have hh := (linear_solution_fourthMoment h hnull t ht).2
  refine hh.trans ?_
  unfold momentConstant momentExponent
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ T from ht) (momentExponent_nonneg N Kb Ks T))) (by positivity)

/-- The genuine finite-horizon state has an actual product-time L⁴ class.
Its fourth moment is bounded by the horizon times the explicit uniform
pointwise fourth-moment constant. -/
theorem linear_solution_time_fourthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    MemLp (stateTimeCut X T) 4 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut X T q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤
        (T : ℝ)*momentConstant N Kb Ks T v0 := by
  let μ := nonnegativeLebesgueMeasure
  letI : IsFiniteMeasure (μ.restrict (Ioc (0 : ℝ≥0) T)) := by
    change IsFiniteMeasure (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
    infer_instance
  let H : ℝ≥0 × Ω → ℝ := fun q => ‖stateTimeCut X T q‖^4
  let C := momentConstant N Kb Ks T v0
  have hC : 0 ≤ C := momentConstant_nonneg N Kb Ks T v0
  have hsm := stateTimeCut_aestronglyMeasurable X h.1 h.2.1 T
  have hHsm : AEStronglyMeasurable H (μ.prod P) := hsm.norm.pow 4
  have hHi (s : ℝ≥0) : Integrable (fun ω => H (s,ω)) P := by
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) T
    · have hm := (linear_solution_fourthMoment h hnull s hs.2).1
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
    exact linear_solution_fourthMoment_uniform h hnull s hs.2
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

theorem stateTimeCut_eq_indicator (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) :
    stateTimeCut X T=(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2) := by
  funext q
  by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T <;> simp [stateTimeCut,hq]

/-- Common-path equality on the actual horizon gives equality of the actual
product-time cutoff functions. -/
theorem stateTimeCut_path_congr {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : ∀ᵐ ω ∂P,∀ t,t ≤ T → X t ω=Y t ω) :
    stateTimeCut X T =ᵐ[nonnegativeLebesgueMeasure.prod P] stateTimeCut Y T := by
  have hp := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae h
  filter_upwards [hp] with q hq
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [stateTimeCut,ht,ite_true,hq q.1 ht.2]
  · simp only [stateTimeCut,ht,ite_false]

/-- The product-time fourth-moment theorem instantiated on the actual
augmented Brownian model, with no null-event or moment premise. -/
theorem linear_solution_time_fourthMoment_augmented {Kb Ks : ℝ≥0}
    (F₀ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {a : Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Ks}
    {D : BrownianDriver N P (NullAugmentation.augment F₀ P)} {v0 : State N}
    {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T) :
    MemLp (stateTimeCut X T) 4 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut X T q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤
        (T : ℝ)*momentConstant N Kb Ks T v0 :=
  linear_solution_time_fourthMoment h
    (fun _ hm hzero => NullAugmentation.augment_null_known_zero F₀ hm hzero)

/-- The explicit fourth-moment constant has the correct quartic scaling
in the actual initial vector, needed for genuine difference quotients. -/
theorem momentConstant_smul (Kb Ks T : ℝ≥0) (c : ℝ) (v0 : State N) :
    momentConstant N Kb Ks T (c • v0)=‖c‖^4*momentConstant N Kb Ks T v0 := by
  unfold momentConstant
  rw [norm_smul,mul_pow]
  ring

end SphericalAging.LinearSDETimeFourthMoment
