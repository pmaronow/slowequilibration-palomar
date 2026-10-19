module

public import SphericalAging.WeightedPicard

public section

/-! Actual strong-solution uniqueness through the proved predictable Picard
classes. In particular, the solution premise is the real drift/matrix-Itô
equation, rather than an assumed fixed-point or pathwise uniqueness field. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.StrongUniqueness
open HardSphereDynamics PredictableItoTime PredictableDriftTime LocalSDE
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem continuous_state_processes_ae_eq_of_fixedTime_on
    {X Y : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (hXc : ∀ᵐ omega ∂P, Continuous (fun t => X t omega))
    (hYc : ∀ᵐ omega ∂P, Continuous (fun t => Y t omega))
    (hfixed : ∀ t, t ≤ T → X t =ᵐ[P] Y t) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → X t omega = Y t omega := by
  have hi : ∀ i : Fin N, ∀ᵐ omega ∂P, ∀ t : ℝ≥0,
      (X (min t T) omega) i = (Y (min t T) omega) i := by
    intro i
    have hx : ∀ᵐ omega ∂P, Continuous (fun t : ℝ≥0 => (X (min t T) omega) i) := hXc.mono (fun omega homega =>
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp homega).comp
        (continuous_id.min continuous_const))
    have hy : ∀ᵐ omega ∂P, Continuous (fun t : ℝ≥0 => (Y (min t T) omega) i) := hYc.mono (fun omega homega =>
      ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp homega).comp
        (continuous_id.min continuous_const))
    exact continuous_processes_ae_eq_of_fixedTime hx hy
      (fun t => (hfixed (min t T) (min_le_right _ _)).fun_comp (fun x => x i))
  filter_upwards [ae_all_iff.mpr hi] with omega homega
  intro t ht
  apply PiLp.ext
  intro i
  simpa only [min_eq_left ht] using homega i t

theorem version_timeCut_eq_picard_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma x0 T U p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        ((initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T U +
          finiteNoisePicardMap D hsigma T U : PredictableStateL2 N F P) :
            Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have hadd := Lp.coeFn_add
    ((initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
      (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  have hadd' := Lp.coeFn_add
    (initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
  filter_upwards [hadd, hadd', initialClass_coeFn (F := F) (P := P) x0 T,
    finiteDriftPicardMap_coeFn hb T U, finiteNoisePicardMap_coeFn D hsigma T U]
    with p hp hp' h0 hbcoe hscoe
  change _ = (((initialClass (F := F) (P := P) x0 T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
    (finiteDriftPicardMap hb T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) +
    (finiteNoisePicardMap D hsigma T U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) p
  rw [hp, Pi.add_apply, hp', Pi.add_apply, h0, hbcoe, hscoe]
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht, mem_univ _⟩,
      indicator_of_mem, ht, ite_true]
    simp only [version, coordinateVersion, add_smul, Finset.sum_add_distrib, state_sum_basis]
  · simp [ht]

section ActualSolution
variable {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P} {T : ℝ≥0}
  (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
    =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
include hXeq

/-- The actual strong integral equation identifies the process with the
continuous Picard version of its own predictable class. -/
theorem strongSolution_eq_version (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N)
    (hX : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X T) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → X t omega = version D hb hsigma x0 T U t omega := by
  rcases hX with ⟨hXa, hXc, hbmem, hsigmamem, hactual⟩
  apply continuous_state_processes_ae_eq_of_fixedTime_on hXc (version_ae_continuous D hb hsigma x0 T U)
  intro t ht
  have hall : ∀ i : Fin N, ∀ᵐ omega ∂P, (X t omega) i = (version D hb hsigma x0 T U t omega) i := by
    intro i
    filter_upwards [hactual t ht i, driftVersion_eq_actual_drift_ae hXeq (hb i),
      actual_driverIto_ae_eq hXeq hXa hXc D (hsigma i) t ht] with omega heq hdrift hnoise
    rw [version_apply]
    rw [hnoise] at heq
    simpa only [coordinateVersion, hdrift t ht] using heq
  filter_upwards [ae_all_iff.mpr hall] with omega homega
  exact PiLp.ext (homega)

/-- Every actual strong solution with a genuine predictable state class
satisfies the actual Picard fixed-point equation. -/
theorem strongSolution_fixedPoint (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N)
    (hX : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X T) :
    U = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U := by
  have hpath := strongSolution_eq_version hXeq D hb hsigma x0 hX
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hpath
  have hcut : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => version D hb hsigma x0 T U p.1 p.2)) := by
    filter_upwards [hprod] with p hp
    by_cases ht : p.1 ∈ Ioc 0 T
    · simp only [show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht, mem_univ _⟩, indicator_of_mem]
      exact hp p.1 ht.2
    · simp [ht]
  apply Subtype.ext
  apply Lp.ext
  exact hXeq.symm.trans (hcut.trans (version_timeCut_eq_picard_ae D hb hsigma x0 T U))
end ActualSolution

@[expose] def stateTimeRestrict (t : ℝ≥0) (U : PredictableStateL2 N F P) : PredictableStateL2 N F P := by
  have hmem : MemLp ((Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator
      (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) 2
        (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).indicator
      (measurableSet_Ioc.prod MeasurableSet.univ)
  refine ⟨hmem.toLp _, ?_⟩
  change AEStronglyMeasurable[F.predictable] (hmem.toLp _ : ℝ≥0 × Ω → State N)
    (nonnegativeLebesgueMeasure.prod P)
  have hm : AEStronglyMeasurable[F.predictable]
      ((Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator
        (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
      (nonnegativeLebesgueMeasure.prod P) := by
    have hpred := lpMeas.aestronglyMeasurable U
    refine ⟨(Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator
      (hpred.mk (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))),
      hpred.stronglyMeasurable_mk.indicator
        (measurableSet_predictable_Ioc_prod (𝓕 := F) 0 t MeasurableSet.univ), ?_⟩
    filter_upwards [hpred.ae_eq_mk] with q hq
    by_cases hqt : q ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) <;> simp [hqt, hq]
  exact hm.congr hmem.coeFn_toLp.symm

theorem stateTimeRestrict_coeFn (t : ℝ≥0) (U : PredictableStateL2 N F P) :
    (stateTimeRestrict t U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator
        (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) := by
  unfold stateTimeRestrict
  exact ((Lp.memLp (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).indicator
    (s := Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω))
    (measurableSet_Ioc.prod MeasurableSet.univ)).coeFn_toLp

theorem stateTimeRestrict_of_process {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P}
    {S T : ℝ≥0} (hST : S ≤ T)
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) :
    ((Ioc (0 : ℝ≥0) S ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (stateTimeRestrict S U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  filter_upwards [hXeq, stateTimeRestrict_coeFn S U] with p hp hrestrict
  rw [hrestrict]
  by_cases hps : p.1 ∈ Ioc 0 S
  · have hpt : p.1 ∈ Ioc 0 T := ⟨hps.1, hps.2.trans hST⟩
    simpa only [indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hpt, mem_univ _⟩),
      indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) S ×ˢ (univ : Set Ω) from ⟨hps, mem_univ _⟩)] using hp
  · simp [hps]

theorem strongSolutions_eq_of_picard_unique (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) (T : ℝ≥0)
    (hunique : ∀ U V : PredictableStateL2 N F P,
      U = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T U + finiteNoisePicardMap D hsigma T U →
      V = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hsigma T V → U=V)
    {X Y : ℝ≥0 → Ω → State N} {U V : PredictableStateL2 N F P}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hYeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => Y p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (V : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hX : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X T)
    (hY : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 Y T) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ T → X t omega = Y t omega := by
  have hUV := hunique U V (strongSolution_fixedPoint hXeq D hb hsigma x0 hX)
    (strongSolution_fixedPoint hYeq D hb hsigma x0 hY)
  have hx := strongSolution_eq_version hXeq D hb hsigma x0 hX
  have hy := strongSolution_eq_version hYeq D hb hsigma x0 hY
  rw [hUV] at hx
  filter_upwards [hx, hy] with omega hxomega hyomega
  intro t ht
  exact (hxomega t ht).trans (hyomega t ht).symm

theorem strongSolution_on_smaller (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) {S T : ℝ≥0} (hST : S ≤ T)
    {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P}
    (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
    (hX : IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X T) :
    IsLocalStrongSolutionOn b sigma (fun i j => (hsigma i j).continuous) D x0 X S := by
  rcases hX with ⟨hXa,hXc,hbmem,hsigmamem,hactual⟩
  refine ⟨hXa,hXc,(fun i => coefficient_timeCut_memLp hXeq (hb i) S hST),
    (fun i j t ht => hsigmamem i j t (ht.trans hST)), ?_⟩
  intro t ht i
  exact hactual t (ht.trans hST) i

/-- Actual constructed solutions on different finite horizons agree on
their common prefix. The premise of fixed-point uniqueness will be supplied
by the proved weighted Banach theorem. -/
theorem picard_versions_compatible (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hsigma : ∀ i j, LipschitzWith Ks (sigma i j))
    (x0 : State N) {S T : ℝ≥0} (hST : S ≤ T) (U V : PredictableStateL2 N F P)
    (_hU : U = initialClass (F := F) (P := P) x0 S + finiteDriftPicardMap hb S U + finiteNoisePicardMap D hsigma S U)
    (hV : V = initialClass (F := F) (P := P) x0 T + finiteDriftPicardMap hb T V + finiteNoisePicardMap D hsigma T V)
    (hunique : ∀ W : PredictableStateL2 N F P,
      W = initialClass (F := F) (P := P) x0 S + finiteDriftPicardMap hb S W + finiteNoisePicardMap D hsigma S W → W=U) :
    ∀ᵐ omega ∂P, ∀ t, t ≤ S → version D hb hsigma x0 T V t omega = version D hb hsigma x0 S U t omega := by
  have hVeq := version_timeCut_eq_fixedPoint_ae D hb hsigma x0 T V hV
  have hXsol := WeightedPicard.strongSolution_of_picard_fixedPoint D hb hsigma x0 T V hV
  have hXsmall := strongSolution_on_smaller D hb hsigma x0 hST hVeq hXsol
  have hXeq := stateTimeRestrict_of_process hST hVeq
  have hWfix := strongSolution_fixedPoint hXeq D hb hsigma x0 hXsmall
  have hWU := hunique (stateTimeRestrict S V) hWfix
  have hpath := strongSolution_eq_version hXeq D hb hsigma x0 hXsmall
  rw [hWU] at hpath
  exact hpath

end SphericalAging.StrongUniqueness
