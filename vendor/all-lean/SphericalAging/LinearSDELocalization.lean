module

public import SphericalAging.LinearSDEFourthMoment
public import SphericalAging.CutoffSphere

public section

/-! Actual stopping and fourth-moment localization for the constructed
bounded predictable linear SDE. Null augmentation is used only to select
all-path continuous versions; the underlying law and Itô maps are unchanged. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.LinearSDELocalization
open HardSphereDynamics PredictableDriftTime LinearVariationalSDE
  PredictableLinearCoefficient VectorIto ClosedHitStopping StoppedSDE StoppedVectorIto
  LinearSDEFourthMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem driftVersion_eq_actual_of_coe {K : ℝ≥0}
    (a : Coefficient (N := N) (F := F) (P := P) K)
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) (A : PredictableProcessL2 F P)
    (hA : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => a.value (s,ω) (X s ω)) T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → driftVersion A T t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), a.value (s.toNNReal,ω) (X s.toNNReal ω) := by
  have hc : cutRepresentative A T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => a.value (s,ω) (X s ω)) T := by
    filter_upwards [representative_ae A,hA] with q hr ha
    unfold cutRepresentative FourPapersCommon.FilteredBrownian.predictableTimeFrame
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),hr,ha]
    · simp [ht,FourPapersCommon.continuousAdaptedTimeCut]
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  intro t ht
  rw [← primitive_eq_real_intervalIntegral (fun q => a.value q (X q.1 q.2)) t ω]
  unfold driftVersion primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hω,ae_restrict_mem measurableSet_Ioc] with r hr hrt
  change cutRepresentative A T (r,ω) =
    FourPapersCommon.continuousAdaptedTimeCut (fun s ω => a.value (s,ω) (X s ω)) T (r,ω) at hr
  rw [hr]
  exact ite_eq_left ⟨hrt.1,hrt.2.trans ht⟩

lemma vectorProcessLp_zero_time (D : BrownianDriver N P F)
    (U : Fin N → PredictableProcessL2 F P) : vectorProcessLp D U 0 = 0 := by
  have hzero (j : Fin N) : FourPapersCommon.FilteredBrownian.predictableTimeRestrict F 0 (U j) = 0 := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F 0 (U j),
      Lp.coeFn_zero ℝ 2 (nonnegativeLebesgueMeasure.prod P)] with q hq hz
    simpa [FourPapersCommon.FilteredBrownian.predictableTimeFrame,hz] using hq
  unfold vectorProcessLp vectorIto
  simp only [hzero,map_zero,Finset.sum_const_zero]

theorem strongSolution_class_equation {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T) :
    ∃ A : Fin N → PredictableProcessL2 F P, ∃ U : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i, (A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s ω => (a i).value (s,ω) (X s ω)) T) ∧
      (∀ i j, (U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s ω => (sigma i j).value (s,ω) (X s ω)) T) ∧
      (∀ t, t ≤ T → ∀ i, ∀ᵐ ω ∂P, X t ω i = v0 i + driftVersion (A i) T t ω + vectorProcess D (U i) t ω) := by
  rcases h with ⟨_,_,A,U,hA,hU,heq⟩
  refine ⟨A,U,hA,hU,?_⟩
  intro t ht i
  have hdrift := driftVersion_eq_actual_of_coe (a i) X T (A i) (hA i)
  have hnoise : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) =
      vectorProcessLp D (U i) t := CutoffSphere.driverItoMap_eq_vectorIto D _
  have hh := heq t ht i
  rw [hnoise] at hh
  filter_upwards [hh,hdrift,vectorProcessLp_ae_eq D (U i) t] with ω hω hd hn
  rw [← hd t ht,hn] at hω
  exact hω

theorem IsStrongSolutionOn.initial {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T) : ∀ᵐ ω ∂P, X 0 ω = v0 := by
  obtain ⟨A,U,_,_,heq⟩ := strongSolution_class_equation h
  have hnoise (i : Fin N) : vectorProcess D (U i) 0 =ᵐ[P] fun _ => (0 : ℝ) := by
    have he := vectorProcessLp_ae_eq D (U i) 0
    rw [vectorProcessLp_zero_time] at he
    exact he.symm.trans (Lp.coeFn_zero ℝ 2 P)
  filter_upwards [ae_all_iff.mpr (fun i => heq 0 bot_le i),ae_all_iff.mpr hnoise] with ω hω hn
  apply PiLp.ext
  intro i
  have hh := hω i
  simp only [driftVersion,primitive,Ioc_self,Measure.restrict_empty,integral_zero_measure,hn i,add_zero] at hh
  exact hh

/-- An actual predictable drift class has a jointly measurable representative
whose every path is integrable and which vanishes beyond the horizon. -/
theorem exists_allPath_integrable_drift (A : PredictableProcessL2 F P) (T : ℝ≥0) :
    ∃ μ : ℝ≥0 → Ω → ℝ, Measurable (Function.uncurry μ) ∧
      (∀ ω, Integrable (fun s => μ s ω) nonnegativeLebesgueMeasure) ∧
      (∀ s ω, s ∉ Ioc (0 : ℝ≥0) T → μ s ω = 0) ∧
      (Function.uncurry μ =ᵐ[nonnegativeLebesgueMeasure.prod P] cutRepresentative A T) := by
  classical
  have hbad : P {ω | ¬ Integrable (fun s => cutRepresentative A T (s,ω)) nonnegativeLebesgueMeasure} = 0 := by
    simpa only [ae_iff] using (cutRepresentative_integrable A T).prod_left_ae
  obtain ⟨B,hsub,hBm,hB0⟩ := exists_measurable_superset_of_null hbad
  let μ : ℝ≥0 → Ω → ℝ := fun s ω => if ω ∈ B then 0 else cutRepresentative A T (s,ω)
  refine ⟨μ,?_,?_,?_,?_⟩
  · exact Measurable.ite (hBm.preimage measurable_snd) measurable_const
      (((cutRepresentative_stronglyMeasurable A T).mono (predictable_le_prod F)).measurable)
  · intro ω
    by_cases hω : ω ∈ B
    · simp [μ,hω]
    · have hi : Integrable (fun s => cutRepresentative A T (s,ω)) nonnegativeLebesgueMeasure := by
        by_contra hn
        exact hω (hsub hn)
      simpa only [μ,hω,ite_false] using hi
  · intro s ω hs
    unfold μ cutRepresentative FourPapersCommon.FilteredBrownian.predictableTimeFrame
    split_ifs <;> simp [hs]
  · have hae : ∀ᵐ ω ∂P, ω ∉ B := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hB0
    have hprod := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hae
    filter_upwards [hprod] with q hq
    change (if q.2 ∈ B then 0 else cutRepresentative A T q) = _
    simp only [hq,ite_false]

/-- Equality of the true finite-horizon class and its predictable representative. -/
theorem cutRepresentative_eq_of_coe (A : PredictableProcessL2 F P) (T : ℝ≥0)
    (f : ℝ≥0 → Ω → ℝ)
    (hA : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut f T) :
    cutRepresentative A T =ᵐ[nonnegativeLebesgueMeasure.prod P] (A : TimeProcessL2 P) := by
  filter_upwards [representative_ae A,hA] with q hr ha
  by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hq,mem_univ _⟩),hr]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false] at ha
    simp [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq,ha]

theorem integratedDrift_eq_of_coe (μ : ℝ≥0 → Ω → ℝ) (A : PredictableProcessL2 F P) (T : ℝ≥0)
    (h : Function.uncurry μ =ᵐ[nonnegativeLebesgueMeasure.prod P] cutRepresentative A T) :
    ∀ᵐ ω ∂P, ∀ t, integratedDrift μ t ω = driftVersion A T t ω := by
  have hs := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae h)
  filter_upwards [hs] with ω hω
  intro t
  rw [← WeightedDriftSums.driftPrimitive_eq_integratedDrift]
  unfold WeightedDriftSums.driftPrimitive driftVersion primitive
  exact integral_congr_ae (ae_restrict_of_ae hω)

/-- The canonical continuous version and the genuine stopped matrix classes
satisfy the radius-independent fourth-moment estimate. -/
theorem exists_localized_fourthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A) :
    ∃ Y : ℝ≥0 → Ω → State N, StronglyAdapted F Y ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ ω,Y 0 ω=v0) ∧
      (∀ᵐ ω ∂P,∀ t,Y t ω=X t ω) ∧
      ∀ R : ℝ≥0, ‖v0‖ ≤ R → ∀ t, t ≤ T →
        (∫ ω, ‖stoppedState Y (radiusHit Y T R) t ω‖^4 ∂P) ≤
          3*‖v0‖^4 * Real.exp ((3*(T : ℝ)*(radialDriftConstant N Kb Ks : ℝ)^2+
            3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ)) := by
  classical
  obtain ⟨Y₁,hY₁a,hY₁c,hY₁X⟩ := NullAugmentation.exists_allPath_continuous_modification
    F hnull X h.1 h.2.1
  have hY₁0 : ∀ᵐ ω ∂P,Y₁ 0 ω=v0 := by
    filter_upwards [hY₁X,IsStrongSolutionOn.initial h] with ω hω h0
    rw [hω 0,h0]
  let Y := CutoffSphere.initialNormalized Y₁ v0
  have hYa := CutoffSphere.initialNormalized_adapted Y₁ v0 hY₁a
  have hYc := CutoffSphere.initialNormalized_continuous Y₁ v0 hY₁c
  have hY0 : ∀ ω,Y 0 ω=v0 := CutoffSphere.initialNormalized_initial Y₁ v0
  have hYX : ∀ᵐ ω ∂P,∀ t,Y t ω=X t ω := by
    filter_upwards [CutoffSphere.initialNormalized_ae Y₁ v0 hY₁0,hY₁X] with ω hω hh
    exact fun t => (hω t).trans (hh t)
  refine ⟨Y,hYa,hYc,hY0,hYX,?_⟩
  obtain ⟨A,U,hA,hU,heq⟩ := strongSolution_class_equation h
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
      ‖(A' i : TimeProcessL2 P) q‖ ≤ Kb*‖Z q.1 q.2‖ := by
    filter_upwards [stoppedIntegrand_coe hτ T (A i),hA i,(a i).bound,hYprod] with q hc ha hb hy
    rw [hc,ha]
    change ‖stoppedTimeCoefficient τ T q * FourPapersCommon.continuousAdaptedTimeCut _ T q‖ ≤ _
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T ∧ q.1 ≤ τ q.2
    · rw [show stoppedTimeCoefficient τ T q=1 from ite_eq_left hq,one_mul]
      rw [show FourPapersCommon.continuousAdaptedTimeCut _ T q=_ from ite_eq_left hq.1]
      have hz : Z q.1 q.2=X q.1 q.2 := by
        dsimp [Z,stoppedState]
        rw [min_eq_left hq.2,hy q.1]
      rw [hz]
      exact (a i).value q |>.le_of_opNorm_le hb _
    · rw [show stoppedTimeCoefficient τ T q=0 from ite_eq_right hq,zero_mul,norm_zero]
      exact mul_nonneg Kb.coe_nonneg (norm_nonneg _)
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
  exact bounded_matrix_fourthMoment D Z hZa hZc R Kb Ks hZbound T v0 A' U' μ'
    hA' hμ'm hμ'int hAb hUb hZ0 hZe t ht

/-- Uniform fourth-moment control survives a genuine almost-sure limit,
by Fatou's lemma. Integrability of the limiting fourth power is proved. -/
theorem fourthMoment_of_ae_tendsto (Z : ℕ → Ω → State N) (Y : Ω → State N) (C : ℝ)
    (hC : 0 ≤ C) (hZm : ∀ n,AEStronglyMeasurable (Z n) P)
    (hYm : AEStronglyMeasurable Y P)
    (hZi : ∀ n,Integrable (fun ω => ‖Z n ω‖^4) P)
    (hbound : ∀ n,(∫ ω,‖Z n ω‖^4 ∂P) ≤ C)
    (hlim : ∀ᵐ ω ∂P,Tendsto (fun n => Z n ω) atTop (𝓝 (Y ω))) :
    Integrable (fun ω => ‖Y ω‖^4) P ∧ (∫ ω,‖Y ω‖^4 ∂P) ≤ C := by
  have hf : AEStronglyMeasurable (fun ω => ‖Y ω‖^4) P := hYm.norm.pow 4
  have hn : 0 ≤ᵐ[P] (fun ω => ‖Y ω‖^4) := .of_forall (fun _ => by positivity)
  have hl : ∀ᵐ ω ∂P,Tendsto (fun n => ENNReal.ofReal (‖Z n ω‖^4)) atTop
      (𝓝 (ENNReal.ofReal (‖Y ω‖^4))) := by
    filter_upwards [hlim] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hω.norm.pow 4)
  have hh : (∫⁻ ω,ENNReal.ofReal (‖Y ω‖^4) ∂P) ≤
      liminf (fun n => ∫⁻ ω,ENNReal.ofReal (‖Z n ω‖^4) ∂P) atTop := by
    calc
      _ = ∫⁻ ω,liminf (fun n => ENNReal.ofReal (‖Z n ω‖^4)) atTop ∂P :=
        lintegral_congr_ae (hl.mono (fun _ h => h.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' (fun n => (hZm n).norm.pow 4 |>.aemeasurable.ennreal_ofReal)
  have hb : liminf (fun n => ∫⁻ ω,ENNReal.ofReal (‖Z n ω‖^4) ∂P) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le _ ⟨0,Eventually.of_forall (fun _ => bot_le)⟩
    exact (Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hZi n) (.of_forall (fun _ => by positivity))]
      exact ENNReal.ofReal_le_ofReal (hbound n))).frequently
  have hfinite := hh.trans hb
  have hi : Integrable (fun ω => ‖Y ω‖^4) P := ⟨hf,
    (hasFiniteIntegral_iff_ofReal hn).mpr (hfinite.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  exact hfinite

/-- Radius hitting is exactly the endpoint once the entire continuous
prefix is strictly inside the radius. -/
theorem radiusHit_eq_horizon_of_bound (Y : ℝ≥0 → Ω → State N)
    (hYc : ∀ ω,Continuous (fun t => Y t ω)) (T R : ℝ≥0) (ω : Ω)
    (hb : ∀ s,s ≤ T → ‖Y s ω‖ < R) : radiusHit Y T R ω=T := by
  apply le_antisymm (radiusHit_le Y hYc T R ω)
  by_contra hn
  have hlt : radiusHit Y T R ω<T := lt_of_not_ge hn
  have hm := (firstClosedHit_isLeast (fun s η => ‖Y s η‖) T R ω ((hYc ω).norm)).1
  rcases hm with ⟨hs,hR⟩ | he
  · exact (not_le_of_gt (hb _ hs.2)) hR
  · exact (ne_of_lt hlt) he

/-- Actual bounded-predictable linear SDE solutions have fourth moments.
All radial identities, stopping equations, and integrability conclusions
are proved; no derivative or moment estimate is supplied as a premise. -/
theorem linear_solution_fourthMoment {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {v0 : State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) :
    MemLp (X t) 4 P ∧ (∫ ω,‖X t ω‖^4 ∂P) ≤
      3*‖v0‖^4 * Real.exp ((3*(T : ℝ)*(radialDriftConstant N Kb Ks : ℝ)^2+
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
  let C : ℝ := 3*‖v0‖^4 * Real.exp ((3*(T : ℝ)*(radialDriftConstant N Kb Ks : ℝ)^2+
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
theorem linear_solution_fourthMoment_augmented {Kb Ks : ℝ≥0}
    (F₀ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {a : Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := NullAugmentation.augment F₀ P) (P := P) Ks}
    {D : BrownianDriver N P (NullAugmentation.augment F₀ P)} {v0 : State N}
    {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D v0 X T) (t : ℝ≥0) (ht : t ≤ T) :
    MemLp (X t) 4 P ∧ (∫ ω,‖X t ω‖^4 ∂P) ≤
      3*‖v0‖^4 * Real.exp ((3*(T : ℝ)*(radialDriftConstant N Kb Ks : ℝ)^2+
        3*N*(radialNoiseConstant N Ks : ℝ)^2)*(t : ℝ)) :=
  linear_solution_fourthMoment h (fun _ hm hzero => NullAugmentation.augment_null_known_zero F₀ hm hzero) t ht

end SphericalAging.LinearSDELocalization
