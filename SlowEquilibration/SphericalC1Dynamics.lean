-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalDynamics

/-! Actual global spherical Langevin solutions for a C¹ ambient gradient.
Compact cutoffs give genuine global Lipschitz coefficients. The radial Itô
argument proves sphere preservation for the constructed Brownian solution. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SlowEquilibration.SphericalC1Dynamics
open SphericalAging SphericalModel SphericalDynamics
open HardSphereDynamics LocalSDE VectorIto SpherePreservation StoppedVectorIto
open ClosedHitStopping StoppedSDE RadialItoRepresentation WeightedDriftSums CutoffSphere
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem contDiff_drift (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (drift β g) := by
  have hp : ContDiff ℝ 1 (fun x : State N => projection x (g x)) := by
    simp only [projection, div_eq_mul_inv]
    exact hg.sub (((contDiff_id.inner ℝ hg).mul contDiff_const).smul contDiff_id)
  exact hp.const_smul β |>.sub (contDiff_id.const_smul (kappa N))

/-- Compactly supported C¹ coefficients, and not an assumed bound, provide
the global Lipschitz constant used by the actual Picard construction. -/
theorem cutoffDrift_lipschitz (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (R : ℝ) (hR : 0<R) :
    ∃ K : ℝ≥0, ∀ i, LipschitzWith K (cutoffDrift β g R hR i) := by
  have hc : ContDiff ℝ 1 (cutoffCoefficient R hR (drift β g)) :=
    (coefficientBump (N := N) R hR).contDiff.smul (contDiff_drift β g hg)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (cutoffCoefficient_hasCompactSupport R hR (drift β g)) hc (by norm_num)
  refine ⟨K,fun i => ?_⟩
  change LipschitzWith K (fun x => (cutoffCoefficient R hR (drift β g) x) i)
  simpa only [one_mul,Function.comp_def] using (CutoffSDE.coordinate_lipschitz i).comp hK

omit [MeasurableSpace Ω] in
lemma stopped_physical_drift_cutoff (β : ℝ) (g : State N → State N) (_hg : ContDiff ℝ 1 g) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (X : ℝ≥0 → Ω → State N) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hbound : ∀ s ω, ‖stoppedState X τ s ω‖ ≤ R) (k : Fin N) (s : ℝ≥0) (ω : Ω) :
    stoppedTimeCoefficient τ T (s, ω) * cutoffDrift β g R hR k (X s ω) =
      stoppedPhysicalDrift β g (stoppedState X τ) τ T k s ω := by
  unfold stoppedPhysicalDrift
  by_cases hs : s ∈ Ioc (0 : ℝ≥0) T ∧ s ≤ τ ω
  · have hY : stoppedState X τ s ω = X s ω := by simp only [stoppedState, min_eq_left hs.2]
    rw [hY]
    rw [cutoffDrift_eq β g R hR _ (hY ▸ hbound s ω)]
  · simp only [stoppedTimeCoefficient, hs, ite_false, zero_mul]

omit [MeasurableSpace Ω] in
lemma stopped_physical_noise_cutoff (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (X : ℝ≥0 → Ω → State N) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hbound : ∀ s ω, ‖stoppedState X τ s ω‖ ≤ R) (k i : Fin N) (q : ℝ≥0 × Ω) :
    stoppedTimeCoefficient τ T q * CutoffSDE.cutoffNoise N R hR k i (X q.1 q.2) =
      stoppedTimeCoefficient τ T q * noiseColumn (stoppedState X τ q.1 q.2) i k := by
  by_cases hs : q.1 ∈ Ioc (0 : ℝ≥0) T ∧ q.1 ≤ τ q.2
  · have hY : stoppedState X τ q.1 q.2 = X q.1 q.2 := by simp only [stoppedState, min_eq_left hs.2]
    rw [hY, CutoffSDE.cutoffNoise_eq N R hR _ (hY ▸ hbound q.1 q.2)]
  · simp only [stoppedTimeCoefficient, hs, ite_false, zero_mul]

/-- The actual all-path continuous cutoff solution starting on the sphere
never leaves it before its horizon. The cutoff radius strictly contains
the sphere; no sphere hypothesis on the evolving state is used. -/
theorem onSphere_of_cutoff_solution (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x0 : State N) (hx0 : OnSphere x0)
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsLocalStrongSolutionOn (cutoffDrift β g R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D x0 X T) (hX0 : ∀ ω, X 0 ω = x0) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω) := by
  rcases hsol with ⟨hXa, hXcae, hbmem, hsigmamem, heq⟩
  let b := cutoffDrift β g R hR
  have hb : ∀ k, Continuous (b k) := by
    obtain ⟨K, hK⟩ := cutoffDrift_lipschitz β g hg R hR
    exact fun k => (hK k).continuous
  let τ := radiusHit X T R
  have hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_radiusHit X hXa hXc T R
  have hτbound : ∀ ω, τ ω ≤ T := radiusHit_le X hXc T R
  let Y := stoppedState X τ
  have hYa : StronglyAdapted F Y := stoppedState_stronglyAdapted X hXa hXc hτ
  have hYc : ∀ ω, Continuous (fun s => Y s ω) := stoppedState_continuous X hXc τ
  have hinitialBound : ∀ ω, ‖X 0 ω‖ ≤ R := by
    intro ω
    rw [hX0 ω]
    have hsq := (onSphere_iff_norm_sq x0).mp hx0
    nlinarith [norm_nonneg x0, R.coe_nonneg]
  have hYbound : ∀ s ω, ‖Y s ω‖ ≤ R := stoppedState_radius_bound X hXc T R hinitialBound
  let A0 (k : Fin N) := coefficientPredictableActual hXa hXcae (hb k) T (hbmem k)
  let U0 (k i : Fin N) := coefficientPredictableActual hXa hXcae (hsigma k i) T (hsigmamem k i T le_rfl)
  let A (k : Fin N) := stoppedIntegrand hτ T (A0 k)
  let U (k i : Fin N) := stoppedIntegrand hτ T (U0 k i)
  have hA : ∀ k, (A k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => stoppedPhysicalDrift β g Y τ T k q.1 q.2 := by
    intro k
    filter_upwards [stoppedIntegrand_coe hτ T (A0 k), (hbmem k).coeFn_toLp] with q hstop hcoef
    change (A0 k : ℝ≥0 × Ω → ℝ) q = _ at hcoef
    rw [hstop, hcoef, stopped_coefficient_cut]
    exact stopped_physical_drift_cutoff β g hg R hR X τ T hYbound k q.1 q.2
  have hU : ∀ k i, (U k i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => stoppedTimeCoefficient τ T q * noiseColumn (Y q.1 q.2) i k := by
    intro k i
    filter_upwards [stoppedIntegrand_coe hτ T (U0 k i), (hsigmamem k i T le_rfl).coeFn_toLp] with q hstop hcoef
    change (U0 k i : ℝ≥0 × Ω → ℝ) q = _ at hcoef
    rw [hstop, hcoef, stopped_coefficient_cut]
    exact stopped_physical_noise_cutoff R hR X τ T hYbound k i q
  have hY0 : ∀ᵐ ω ∂P, OnSphere (Y 0 ω) := .of_forall (fun ω => by
    simpa only [Y, stoppedState, min_eq_left (zero_le : (0 : ℝ≥0) ≤ τ ω), hX0 ω] using hx0)
  have hdecomp : ∀ k s, coordinates Y k s =ᵐ[P] fun ω => coordinates Y k 0 ω +
      integratedDrift (stoppedPhysicalDrift β g Y τ T k) s ω + vectorProcess D (U k) s ω := by
    intro k s
    obtain ⟨M, hM⟩ := exists_continuousModification_vectorProcess D (U0 k)
    have hfixed : ∀ t, t ≤ T → (fun ω => X t ω k) =ᵐ[P] fun ω => X 0 ω k +
        integratedDrift (cutDrift b X T k) t ω + M t ω := by
      intro t ht
      have hnoise : driverItoMap D (fun i => coefficientPredictableActual hXa hXcae (hsigma k i) t
          (hsigmamem k i t ht)) = vectorProcessLp D (U0 k) t := by
        rw [driverItoMap_eq_vectorIto]
        unfold vectorProcessLp
        congr 1
        funext i
        exact (coefficientPredictableActual_timeRestrict hXa hXcae (hsigma k i) T t ht _ _).symm
      have hi := (vectorProcessLp_ae_eq D (U0 k) t).trans (hM.fixedTime_ae_eq t)
      have htEq := heq t ht k
      rw [hnoise] at htEq
      filter_upwards [htEq, hi] with ω hω hi
      rw [hX0 ω, integratedDrift_cutDrift b X T t ht k ω]
      simpa only [b, hi] using hω
    have hstop := stopped_equation D hτ T hτbound (U0 k) (fun t ω => X t ω k)
      (cutDrift b X T k) M (fun ω => (CutoffSDE.coordinate_lipschitz k).continuous.comp (hXc ω))
      (cutDrift_integrable b hb X hXc T k) hM.fixedTime_ae_eq hM.continuous_paths hfixed s
    filter_upwards [hstop] with ω hω
    simp only [coordinates, Y, stoppedState, zero_min]
    rw [hω]
    congr 1
    congr 1
    apply congrArg (fun f => integratedDrift f s ω)
    funext r η
    rw [stopped_cutDrift_eq]
    exact stopped_physical_drift_cutoff β g hg R hR X τ T hYbound k r η
  have hYsphere := bounded_stopped_physical_solution_onSphere hN D β g
    hg.continuous Y hYa hYc R hR hYbound τ hτ T A U hA hU hY0 hdecomp
  filter_upwards [hYsphere] with ω hω
  have hτeq : τ ω = T := by
    apply le_antisymm (hτbound ω)
    by_contra h
    have hτlt : τ ω < T := lt_of_not_ge h
    have hr := radius_eq_at_hit X hXc T R hinitialBound ω hτlt
    have hYhit := (onSphere_iff_norm_sq (Y (τ ω) ω)).mp (hω (τ ω) (hτbound ω))
    simp only [Y, stoppedState, min_self] at hYhit
    rw [hr] at hYhit
    linarith
  intro t ht
  have hs := hω t ht
  simpa only [Y, stoppedState, hτeq, min_eq_left ht] using hs

theorem onSphere_of_cutoff_solution_aeInitial (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x0 : State N) (hx0 : OnSphere x0)
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsLocalStrongSolutionOn (cutoffDrift β g R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D x0 X T) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω) := by
  have hXinit := hsol.initial
  have hsolCopy := hsol
  obtain ⟨hXa, hXcae, hb, hsig, heq⟩ := hsol
  let Y := initialNormalized X x0
  have hYa := initialNormalized_adapted X x0 hXa
  have hYc := initialNormalized_continuous X x0 hXc
  have hYX := initialNormalized_ae X x0 hXinit
  have hYsol := AllPathSDE.IsLocalStrongSolutionOn.path_congr hsolCopy hYa (.of_forall hYc) hYX
  have hYsphere := onSphere_of_cutoff_solution hN D β g hg R hR hNR x0 hx0 Y hYc T hsigma hYsol
    (initialNormalized_initial X x0)
  filter_upwards [hYsphere, hYX] with ω hω hYXω
  intro t ht
  have hs := hω t ht
  change OnSphere (initialNormalized X x0 t ω) at hs
  simpa only [hYXω t] using hs

theorem physical_solution_of_cutoff (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x0 : State N) (hx0 : OnSphere x0)
    (X : ℝ≥0 → Ω → State N) (hXc : ∀ ω, Continuous (fun s => X s ω))
    (T : ℝ≥0) (hsigma : ∀ i j, Continuous (CutoffSDE.cutoffNoise N R hR i j))
    (hsol : IsLocalStrongSolutionOn (cutoffDrift β g R hR) (CutoffSDE.cutoffNoise N R hR)
      hsigma D x0 X T) :
    IsLocalStrongSolutionOn (fun i x => drift β g x i) (fun i j x => noiseColumn x j i)
      physical_noise_continuous D x0 X T ∧ (∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere (X t ω)) := by
  have hSphere := onSphere_of_cutoff_solution_aeInitial hN D β g hg R hR hNR x0 hx0 X hXc T hsigma hsol
  have hbound : ∀ᵐ ω ∂P, ∀ t, t ≤ T → ‖X t ω‖ ≤ R := by
    filter_upwards [hSphere] with ω hω
    intro t ht
    have hsq := (onSphere_iff_norm_sq (X t ω)).mp (hω t ht)
    nlinarith [norm_nonneg (X t ω), R.coe_nonneg]
  refine ⟨coefficient_congr_onPath physical_noise_continuous hsol ?_ ?_, hSphere⟩
  · intro i
    filter_upwards [hbound] with ω hω
    intro t ht
    exact (cutoffDrift_eq β g R hR _ (hω t ht) i).symm
  · intro i j
    filter_upwards [hbound] with ω hω
    intro t ht
    exact (CutoffSDE.cutoffNoise_eq N R hR _ (hω t ht) i j).symm



/-- A finite-horizon Picard solution of an arbitrary C¹ projected drift
stays on the sphere. Its invariance is derived from the generic radial Ito
argument, with all-path modifications supplied by null augmentation. -/
theorem horizonProcess_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ) ^ 2)
    (x : State N) (hx : OnSphere x) (T : ℝ≥0) {Kb Ks : ℝ≥0}
    (hb : ∀ i, LipschitzWith Kb (cutoffDrift β g R hR i))
    (hs : ∀ i j, LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → OnSphere
      (GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x T t ω) := by
  let D := NullAugmentation.driver D₀
  let X := GlobalSDE.horizonProcess D hb hs x T
  obtain ⟨Y, hYa, hYc, hYX⟩ := NullAugmentation.exists_allPath_continuous_modification_augmented
    F X (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
      (GlobalSDE.horizonProcess_continuous D hb hs x T)
  have hYsol := AllPathSDE.IsLocalStrongSolutionOn.path_congr
    (GlobalSDE.horizonProcess_strongSolution D hb hs x T) hYa (.of_forall hYc) hYX
  have hYs := (physical_solution_of_cutoff hN D β g hg R hR hNR x hx Y hYc T
    (fun i j => (hs i j).continuous) hYsol).2
  filter_upwards [hYs, hYX] with ω hω he
  intro t ht
  change OnSphere (X t ω)
  rw [← he t]
  exact hω t ht


/-- Canonical genuine Brownian-path cutoff solution for the C¹ gradient. -/
def process (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) : ℝ≥0 → VectorBrownian.Space N → State N :=
  GlobalSDE.process (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β g hg
      (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x

/-- Sphere preservation on one common event for every nonnegative time. -/
theorem process_onSphere (hN : N ≠ 0) (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) (hx : OnSphere x) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, OnSphere (process β g hg x t ω) := by
  have hall := ae_all_iff.mpr (fun n : ℕ => horizonProcess_onSphere hN
    (VectorBrownian.driver N) β g hg
    (cutoffRadius N) (cutoffRadius_pos N) (cutoffRadius_contains_sphere N) x hx
    (GlobalSDE.integerHorizon n)
    (cutoffDrift_lipschitz β _ hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec)
  filter_upwards [hall] with ω hω
  intro t
  exact hω (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)

/-- The constructed process satisfies the actual untruncated C¹ Langevin
SDE, with real time integrals and the genuine independent coordinate Ito
integrals. No sphere-support or generator premise is assumed. -/
theorem process_physical (hN : N ≠ 0) (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    IsLocalStrongSolutionOn (fun i z => drift β g z i)
      (fun i j z => noiseColumn z j i) physical_noise_continuous
      (NullAugmentation.driver (VectorBrownian.driver N)) x (process β g hg x) T := by
  have hbound : ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, ‖process β g hg x t ω‖ ≤ cutoffRadius N := by
    filter_upwards [process_onSphere hN β g hg x hx] with ω hω
    intro t
    have hsq := (onSphere_iff_norm_sq _).mp (hω t)
    nlinarith [norm_nonneg (process β g hg x t ω), (cutoffRadius N).coe_nonneg,
      cutoffRadius_contains_sphere N]
  have hcut := GlobalSDE.process_strongSolution
    (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β _ hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x T
  exact coefficient_congr_onPath physical_noise_continuous hcut
    (fun i => hbound.mono (fun ω h t _ =>
      (cutoffDrift_eq β g _ (cutoffRadius_pos N) _ (h t) i).symm))
    (fun i j => hbound.mono (fun ω h t _ =>
      (CutoffSDE.cutoffNoise_eq N _ (cutoffRadius_pos N) _ (h t) i j).symm))

/-- Actual continuous paths for every initial state, without a form-domain premise. -/
theorem process_continuous (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) :
    ∀ᵐ ω ∂VectorBrownian.law N, Continuous (fun t => process β g hg x t ω) :=
  GlobalSDE.process_continuous _ _ _ x

theorem process_measurable (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) (t : ℝ≥0) : Measurable (process β g hg x t) :=
  ((GlobalSDE.process_stronglyAdapted _ _ _ x t).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le t)).measurable

/-- Probability law of the actual terminal C¹ Langevin state. -/
def transitionLaw (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) (x : State N) : Measure (State N) :=
  (VectorBrownian.law N).map (process β g hg x t)

instance transitionLaw_probability (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) (x : State N) :
    IsProbabilityMeasure (transitionLaw β g hg t x) := by
  unfold transitionLaw
  infer_instance

theorem process_zero (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) :
    process β g hg x 0 =ᵐ[VectorBrownian.law N] fun _ => x :=
  (GlobalSDE.process_strongSolution
    (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β _ hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x 0).initial

/-- Zero time is the actual point-mass kernel law. -/
theorem transitionLaw_zero (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) : transitionLaw β g hg 0 x = Measure.dirac x := by
  rw [transitionLaw, Measure.map_congr (process_zero β g hg x),
    Measure.map_const, measure_univ, one_smul]

/-- Every physical initial state has a transition probability fully supported
on the radius-`sqrt N` sphere, for every nonnegative time. -/
theorem transitionLaw_support (hN : N ≠ 0) (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    transitionLaw β g hg t x {y : State N | OnSphere y} = 1 := by
  rw [transitionLaw, Measure.map_apply (process_measurable β g hg x t)
    (sphere_measurableSet N)]
  calc
    _ = (VectorBrownian.law N) Set.univ := by
      apply measure_congr
      filter_upwards [process_onSphere hN β g hg x hx] with ω hω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ]
      simp [hω t]
    _ = 1 := measure_univ


/-- Actual global coefficient bounds for the C¹ cutoff.
These are proved from compact support of the cutoff and the literal noise. -/
def coefficientBounds (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) :
    FixedCoefficients.CoefficientBounds
      (cutoffDrift β g (cutoffRadius N) (cutoffRadius_pos N))
      (CutoffSDE.cutoffNoise N (cutoffRadius N) (cutoffRadius_pos N)) := by
  let hd := cutoffCoefficient_bounded (cutoffRadius N) (cutoffRadius_pos N)
    (drift β g) (contDiff_drift β _ hg).continuous
  let hn := CutoffSDE.cutoffNoise_bounded N (cutoffRadius N) (cutoffRadius_pos N)
  exact ⟨⟨max hd.choose 0, le_max_right _ _⟩, hn.choose,
    (fun i x => ((PiLp.norm_apply_le _ i).trans (hd.choose_spec x)).trans (le_max_left _ _)),
    hn.choose_spec⟩

/-- The actual C¹ Langevin transitions form a genuine measurable Markov
kernel; joint measurability was derived from the actual Picard family. -/
def transitionKernel (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) : Kernel (State N) (State N) :=
  FixedCoefficients.transitionKernel (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β _ hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec t

instance transitionKernel_markov (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) : IsMarkovKernel (transitionKernel β g hg t) :=
  FixedCoefficients.transitionKernel_markov _ _ _ _

/-- The measurable Markov kernel equals the law of the literal solution. -/
theorem transitionKernel_apply (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (t : ℝ≥0) (x : State N) :
    transitionKernel β g hg t x = transitionLaw β g hg t x :=
  FixedCoefficients.transitionKernel_apply _ _ _ _ _

theorem transitionKernel_zero (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) : transitionKernel β g hg 0 x = Measure.dirac x := by
  rw [transitionKernel_apply, transitionLaw_zero]

theorem transitionKernel_support (hN : N ≠ 0) (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    transitionKernel β g hg t x {y : State N | OnSphere y} = 1 := by
  rw [transitionKernel_apply]
  exact transitionLaw_support hN β g hg x hx t

/-- The actual C¹ Langevin kernels satisfy the literal
Chapman–Kolmogorov identity. No homogeneous-parity restriction is imposed. -/
theorem transitionKernel_semigroup (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g) (s t : ℝ≥0) (x : State N) :
    transitionKernel β g hg (s + t) x =
      (transitionKernel β g hg t ∘ₖ transitionKernel β g hg s) x :=
  FixedCoefficients.transitionKernel_semigroup
    (cutoffDrift_lipschitz β _ hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec
    (coefficientBounds β g hg) s t x

/-- Genuine pathwise uniqueness for the actual globally Lipschitz cutoff
SDE, obtained from Picard uniqueness and the derived predictable state classes. -/
theorem cutoffSolution_unique (D : BrownianDriver N P F) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N)
    (T : ℝ≥0) (X Y : ℝ≥0 → Ω → State N)
    (hX : IsLocalStrongSolutionOn
      (cutoffDrift β g (cutoffRadius N) (cutoffRadius_pos N))
      (CutoffSDE.cutoffNoise N (cutoffRadius N) (cutoffRadius_pos N))
      (fun i j => ((CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N)
        (cutoffRadius_pos N)).choose_spec i j).continuous) D x X T)
    (hY : IsLocalStrongSolutionOn
      (cutoffDrift β g (cutoffRadius N) (cutoffRadius_pos N))
      (CutoffSDE.cutoffNoise N (cutoffRadius N) (cutoffRadius_pos N))
      (fun i j => ((CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N)
        (cutoffRadius_pos N)).choose_spec i j).continuous) D x Y T) :
    ∀ᵐ omega ∂P,∀ t,t≤T → X t omega=Y t omega := by
  let hb := (cutoffDrift_lipschitz β g hg (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
  let hs := (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
  exact RandomSDEStateClass.randomStrongSolutions_unique D hb hs (fun _ => x)
    (memLp_const x) X Y T
    (RandomSDEConversions.localStrongSolution_to_random (fun i => (hb i).continuous) hX)
    (RandomSDEConversions.localStrongSolution_to_random (fun i => (hb i).continuous) hY)

/-- The physical SDE is pathwise unique among sphere-valued solutions.
The cutoffs disappear along both paths, and genuine global Picard uniqueness
then gives equality on the entire horizon. -/
theorem physicalSolution_unique (D : BrownianDriver N P F) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g) (x : State N)
    (T : ℝ≥0) (X Y : ℝ≥0 → Ω → State N)
    (hX : IsLocalStrongSolutionOn (fun i z => drift β g z i)
      (fun i j z => noiseColumn z j i) physical_noise_continuous D x X T)
    (hY : IsLocalStrongSolutionOn (fun i z => drift β g z i)
      (fun i j z => noiseColumn z j i) physical_noise_continuous D x Y T)
    (hXs : ∀ᵐ omega ∂P,∀ t,t≤T → OnSphere (X t omega))
    (hYs : ∀ᵐ omega ∂P,∀ t,t≤T → OnSphere (Y t omega)) :
    ∀ᵐ omega ∂P,∀ t,t≤T → X t omega=Y t omega := by
  have toCut (Z : ℝ≥0 → Ω → State N)
      (hZ : IsLocalStrongSolutionOn (fun i z => drift β g z i)
        (fun i j z => noiseColumn z j i) physical_noise_continuous D x Z T)
      (hZs : ∀ᵐ omega ∂P,∀ t,t≤T → OnSphere (Z t omega)) := by
    have hb : ∀ᵐ omega ∂P,∀ t,t≤T → ‖Z t omega‖≤cutoffRadius N := by
      filter_upwards [hZs] with omega homega
      intro t ht
      have hsq := (onSphere_iff_norm_sq _).mp (homega t ht)
      nlinarith [norm_nonneg (Z t omega),(cutoffRadius N).coe_nonneg,cutoffRadius_contains_sphere N]
    exact coefficient_congr_onPath
      (fun i j => ((CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N)
        (cutoffRadius_pos N)).choose_spec i j).continuous) hZ
      (fun i => hb.mono (fun omega h t ht =>
        cutoffDrift_eq β g _ (cutoffRadius_pos N) _ (h t ht) i))
      (fun i j => hb.mono (fun omega h t ht =>
        CutoffSDE.cutoffNoise_eq N _ (cutoffRadius_pos N) _ (h t ht) i j))
  exact cutoffSolution_unique D β g hg x T X Y (toCut X hX hXs) (toCut Y hY hYs)

end SlowEquilibration.SphericalC1Dynamics
