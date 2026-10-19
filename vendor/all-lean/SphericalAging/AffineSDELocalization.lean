module

public import SphericalAging.AffineSDEFourthMoment

public section

/-! Genuine stopped localization and fourth moments for bounded predictable
affine SDEs. The drift forcing is included in the actual integral equation;
no moment or derivative hypothesis is introduced. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AffineSDELocalization
open HardSphereDynamics PredictableDriftTime InhomogeneousLinearSDE
  PredictableLinearCoefficient VectorIto ClosedHitStopping StoppedSDE StoppedVectorIto
  LinearSDEFourthMoment LinearSDELocalization AffineSDEFourthMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
/-- The canonical continuous version and the genuine stopped matrix classes
satisfy the radius-independent fourth-moment estimate. -/
theorem exists_localized_fourthMoment {Kb Ks B : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A) :
    ∃ Y : ℝ≥0 → Ω → State N, StronglyAdapted F Y ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ ω,Y 0 ω=v0) ∧
      (∀ᵐ ω ∂P,∀ t,Y t ω=X t ω) ∧
      ∀ R : ℝ≥0, ‖v0‖ ≤ R → ∀ t, t ≤ T →
        (∫ ω, ‖stoppedState Y (radiusHit Y T R) t ω‖^4 ∂P) ≤
          3*((B : ℝ)^2+‖v0‖^2)^2 * Real.exp ((3*(T : ℝ)*(affineRadialDriftConstant N Kb Ks : ℝ)^2+
            3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ)) := by
  classical
  obtain ⟨Y₁,hY₁a,hY₁c,hY₁X⟩ := NullAugmentation.exists_allPath_continuous_modification
    F hnull X h.1 h.2.1
  have hY₁0 : ∀ᵐ ω ∂P,Y₁ 0 ω=v0 := by
    filter_upwards [hY₁X,InhomogeneousLinearSDE.IsStrongSolutionOn.initial h] with ω hω h0
    rw [hω 0,h0]
  let Y := CutoffSphere.initialNormalized Y₁ v0
  have hYa := CutoffSphere.initialNormalized_adapted Y₁ v0 hY₁a
  have hYc := CutoffSphere.initialNormalized_continuous Y₁ v0 hY₁c
  have hY0 : ∀ ω,Y 0 ω=v0 := CutoffSphere.initialNormalized_initial Y₁ v0
  have hYX : ∀ᵐ ω ∂P,∀ t,Y t ω=X t ω := by
    filter_upwards [CutoffSphere.initialNormalized_ae Y₁ v0 hY₁0,hY₁X] with ω hω hh
    exact fun t => (hω t).trans (hh t)
  refine ⟨Y,hYa,hYc,hY0,hYX,?_⟩
  obtain ⟨A,U,hA,hU,heq⟩ := InhomogeneousLinearSDE.strongSolution_class_equation h
  have hμchoice (i : Fin N) := exists_allPath_integrable_drift (A i) T
  choose μ hμm hμint hμsupport hμcoe using hμchoice
  have hμA (i : Fin N) : Function.uncurry (μ i) =ᵐ[nonnegativeLebesgueMeasure.prod P] (A i : TimeProcessL2 P) :=
    (hμcoe i).trans (cutRepresentative_eq_of_coe (A i) T _ (hA i))
  have hd (i : Fin N) := integratedDrift_eq_of_coe (μ i) (A i) T (hμcoe i)
  have hMchoice (i : Fin N) := exists_continuousModification_vectorProcess D (U i)
  choose M hM using hMchoice
  have hfixed (i : Fin N) (s : ℝ≥0) (hs : s ≤ T) :
      SpherePreservation.coordinates Y i s =ᵐ[P] fun ω =>
        SpherePreservation.coordinates Y i 0 ω + integratedDrift (μ i) s ω + M i s ω := by
    filter_upwards [heq s hs i,hYX,hd i,(hM i).fixedTime_ae_eq s] with ω hh hy hd hm
    change Y s ω i=Y 0 ω i+integratedDrift (μ i) s ω+M i s ω
    rw [hy s,hY0 ω,hd s,← hm]
    exact hh
  intro R hR t ht
  let τ := radiusHit Y T R
  have hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_radiusHit Y hYa hYc T R
  have hτT : ∀ ω,τ ω ≤ T := radiusHit_le Y hYc T R
  let Z := stoppedState Y τ
  have hZa := stoppedState_stronglyAdapted Y hYa hYc hτ
  have hZc := stoppedState_continuous Y hYc τ
  have hZbound : ∀ s ω,‖Z s ω‖ ≤ R := stoppedState_radius_bound Y hYc T R
    (fun ω => by rw [hY0 ω];exact hR)
  let A' (i : Fin N) := stoppedIntegrand hτ T (A i)
  let U' (i j : Fin N) := stoppedIntegrand hτ T (U i j)
  let μ' (i : Fin N) := stoppedDrift (μ i) τ
  have hμ'coeff (i : Fin N) (q : ℝ≥0 × Ω) :
      μ' i q.1 q.2=stoppedTimeCoefficient τ T q*μ i q.1 q.2 := by
    unfold μ' stoppedDrift stoppedTimeCoefficient
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · by_cases hτq : q.1 ≤ τ q.2 <;> simp [hq,hτq]
    · simp [hq,hμsupport i q.1 q.2 hq]
  have hA' (i : Fin N) : (A' i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ' i q.1 q.2 := by
    filter_upwards [stoppedIntegrand_coe hτ T (A i),hμA i] with q hc hm
    rw [hc,← hm,hμ'coeff]
    rfl
  have hμ'm (i : Fin N) : Measurable (Function.uncurry (μ' i)) := by
    have he : Function.uncurry (μ' i)=fun q => stoppedTimeCoefficient τ T q*μ i q.1 q.2 :=
      funext (hμ'coeff i)
    rw [he]
    exact (((stronglyMeasurable_stoppedTimeCoefficient hτ T).mono (predictable_le_prod F)).measurable).mul (hμm i)
  have hμ'int (i : Fin N) (s : ℝ≥0) : ∀ᵐ ω ∂P,
      IntegrableOn (fun r => μ' i r ω) (Ioc 0 s) nonnegativeLebesgueMeasure := .of_forall (fun ω => by
    have hi := (hμint i ω).indicator (s := Iic (τ ω)) measurableSet_Iic
    convert hi.integrableOn (s := Ioc 0 s) using 1
    funext r
    simp only [μ',stoppedDrift,Set.indicator,mem_Iic])
  have hYprod := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hYX
  have hAb (i : Fin N) : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(A' i : TimeProcessL2 P) q‖ ≤ Kb*‖Z q.1 q.2‖+B := by
    filter_upwards [stoppedIntegrand_coe hτ T (A i),hA i,(a i).bound,(forcing i).bound,hYprod] with q hc ha hb hf hy
    rw [hc,ha]
    change ‖stoppedTimeCoefficient τ T q * FourPapersCommon.continuousAdaptedTimeCut _ T q‖ ≤ _
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T ∧ q.1 ≤ τ q.2
    · rw [show stoppedTimeCoefficient τ T q=1 from ite_eq_left hq,one_mul]
      rw [show FourPapersCommon.continuousAdaptedTimeCut _ T q=_ from ite_eq_left hq.1]
      have hz : Z q.1 q.2=X q.1 q.2 := by
        dsimp [Z,stoppedState]
        rw [min_eq_left hq.2,hy q.1]
      rw [hz]
      exact (norm_add_le _ _).trans (add_le_add ((a i).value q |>.le_of_opNorm_le hb _) hf)
    · rw [show stoppedTimeCoefficient τ T q=0 from ite_eq_right hq,zero_mul,norm_zero]
      exact add_nonneg (mul_nonneg Kb.coe_nonneg (norm_nonneg _)) B.coe_nonneg
  have hUb (i j : Fin N) : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U' i j : TimeProcessL2 P) q‖ ≤ Ks*‖Z q.1 q.2‖ := by
    filter_upwards [stoppedIntegrand_coe hτ T (U i j),hU i j,(sigma i j).bound,hYprod] with q hc ha hb hy
    rw [hc,ha]
    change ‖stoppedTimeCoefficient τ T q * FourPapersCommon.continuousAdaptedTimeCut _ T q‖ ≤ _
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T ∧ q.1 ≤ τ q.2
    · rw [show stoppedTimeCoefficient τ T q=1 from ite_eq_left hq,one_mul]
      rw [show FourPapersCommon.continuousAdaptedTimeCut _ T q=_ from ite_eq_left hq.1]
      have hz : Z q.1 q.2=X q.1 q.2 := by
        dsimp [Z,stoppedState]
        rw [min_eq_left hq.2,hy q.1]
      rw [hz]
      exact (sigma i j).value q |>.le_of_opNorm_le hb _
    · rw [show stoppedTimeCoefficient τ T q=0 from ite_eq_right hq,zero_mul,norm_zero]
      exact mul_nonneg Ks.coe_nonneg (norm_nonneg _)
  have hZ0 : ∀ᵐ ω ∂P,Z 0 ω=v0 := .of_forall (fun ω => by
    dsimp [Z,stoppedState]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ τ ω from bot_le),hY0 ω])
  have hZe (i : Fin N) (s : ℝ≥0) : SpherePreservation.coordinates Z i s =ᵐ[P] fun ω =>
      SpherePreservation.coordinates Z i 0 ω+integratedDrift (μ' i) s ω+vectorProcess D (U' i) s ω := by
    have hh := stopped_equation D hτ T hτT (U i) (SpherePreservation.coordinates Y i) (μ i) (M i)
      (fun ω => (CutoffSDE.coordinate_lipschitz i).continuous.comp (hYc ω))
      (fun ω => (hμint i ω).integrableOn) (hM i).fixedTime_ae_eq (hM i).continuous_paths
      (hfixed i) s
    change (fun ω => Y (min s (τ ω)) ω i) =ᵐ[P] fun ω =>
      Y (min 0 (τ ω)) ω i+integratedDrift (μ' i) s ω+vectorProcess D (U' i) s ω
    simpa only [SpherePreservation.coordinates,μ',U',min_eq_left (show (0 : ℝ≥0) ≤ τ _ from bot_le)] using hh
  exact bounded_affine_fourthMoment D Z hZa hZc R Kb Ks B hZbound T v0 A' U' μ'
    hA' hμ'm hμ'int hAb hUb hZ0 hZe t ht

/-- Actual bounded-predictable linear SDE solutions have fourth moments.
All radial identities, stopping equations, and integrability conclusions
are proved; no derivative or moment estimate is supplied as a premise. -/
theorem affine_solution_fourthMoment {Kb Ks B : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {forcing : Fin N → Forcing (F := F) (P := P) B}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) :
    MemLp (X t) 4 P ∧ (∫ ω,‖X t ω‖^4 ∂P) ≤
      3*((B : ℝ)^2+‖v0‖^2)^2 * Real.exp ((3*(T : ℝ)*(affineRadialDriftConstant N Kb Ks : ℝ)^2+
        3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ)) := by
  obtain ⟨Y,hYa,hYc,hY0,hYX,hbound⟩ := exists_localized_fourthMoment h hnull
  let R (n : ℕ) : ℝ≥0 := ⟨‖v0‖+n+1,by positivity⟩
  have hR (n : ℕ) : ‖v0‖ ≤ R n := by
    change ‖v0‖ ≤ ‖v0‖+(n : ℝ)+1
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  let Z (n : ℕ) : Ω → State N := stoppedState Y (radiusHit Y T (R n)) t
  have hZa (n : ℕ) : StronglyMeasurable[F t] (Z n) :=
    stoppedState_stronglyAdapted Y hYa hYc (isStoppingTime_radiusHit Y hYa hYc T (R n)) t
  have hZm (n : ℕ) : AEStronglyMeasurable (Z n) P := ((hZa n).mono (F.le t)).aestronglyMeasurable
  have hZi (n : ℕ) : Integrable (fun ω => ‖Z n ω‖^4) P := by
    have hm : MemLp (Z n) 4 P := MemLp.of_bound (hZm n) (R n)
      (.of_forall (fun ω => stoppedState_radius_bound Y hYc T (R n)
        (fun η => by rw [hY0 η];exact hR n) t ω))
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.rpow_natCast] using hm.integrable_norm_rpow' 
  have hlim : ∀ᵐ ω ∂P,Tendsto (fun n => Z n ω) atTop (𝓝 (Y t ω)) := .of_forall (fun ω => by
    obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      ((hYc ω).norm.continuousOn)
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hev : ∀ᶠ k : ℕ in atTop,Z k ω=Y t ω := by
      filter_upwards [eventually_ge_atTop n] with k hk
      have hk' : (n : ℝ) ≤ k := by exact_mod_cast hk
      have hMR : M < R k := by
        change M < ‖v0‖+(k : ℝ)+1
        nlinarith [norm_nonneg v0]
      have hτ : radiusHit Y T (R k) ω=T := radiusHit_eq_horizon_of_bound Y hYc T (R k) ω
        (fun s hs => by
          have hh := hM s ⟨bot_le,hs⟩
          rw [Real.norm_of_nonneg (norm_nonneg _)] at hh
          exact hh.trans_lt hMR)
      simp only [Z,stoppedState,hτ,min_eq_left ht]
    exact tendsto_const_nhds.congr' (hev.mono (fun _ hh => hh.symm)))
  let C : ℝ := 3*((B : ℝ)^2+‖v0‖^2)^2 * Real.exp ((3*(T : ℝ)*(affineRadialDriftConstant N Kb Ks : ℝ)^2+
        3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ))
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hi := fourthMoment_of_ae_tendsto Z (Y t) C hC hZm
    ((hYa t).mono (F.le t)).aestronglyMeasurable hZi (fun n => hbound (R n) (hR n) t ht) hlim
  have hXt : Y t =ᵐ[P] X t := hYX.mono (fun _ hh => hh t)
  have hpow : (fun ω => ‖Y t ω‖^4) =ᵐ[P] (fun ω => ‖X t ω‖^4) :=
    hXt.mono (fun ω hh => by
      change ‖Y t ω‖^4=‖X t ω‖^4
      rw [hh])
  have hXi : Integrable (fun ω => ‖X t ω‖^4) P := hi.1.congr hpow
  refine ⟨?_,?_⟩
  · apply (integrable_norm_rpow_iff ((h.1 t).mono (F.le t)).aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.rpow_natCast] using hXi
  · rw [← integral_congr_ae hpow]
    exact hi.2

/-- The concrete augmented Brownian model satisfies the only null-event
condition used to obtain the actual linear fourth moment. -/
theorem affine_solution_fourthMoment_augmented {Kb Ks B : ℝ≥0}
    (F₀ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {a : Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Ks}
    {forcing : Fin N → Forcing (F := NullAugmentation.augment F₀ P) (P := P) B}
    {D : BrownianDriver N P (NullAugmentation.augment F₀ P)} {v0 : State N}
    {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma forcing D v0 X T) (t : ℝ≥0) (ht : t ≤ T) :
    MemLp (X t) 4 P ∧ (∫ ω,‖X t ω‖^4 ∂P) ≤
      3*((B : ℝ)^2+‖v0‖^2)^2 * Real.exp ((3*(T : ℝ)*(affineRadialDriftConstant N Kb Ks : ℝ)^2+
        3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ)) :=
  affine_solution_fourthMoment h (fun _ hm hzero => NullAugmentation.augment_null_known_zero F₀ hm hzero) t ht

end SphericalAging.AffineSDELocalization
