-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import SphericalAging.GlobalHardSphere
public import SphericalAging.JointAdaptedContinuous
public import SphericalAging.PredictableTerminalOperators
public import SphericalAging.PicardDependence
public import SphericalAging.ActualSphereKernelLaw
public import SphericalAging.RandomSDEStateClass

@[expose] public section

/-!
# Actual finite mixed spherical Langevin coefficients and solutions

The all-lean homogeneous Hamiltonian providers do not by themselves accept
mixtures containing both odd and even degrees. This file adapts their generic
Picard and radial-Itô construction to the actual smooth mixed gradient. The
physical drift and projection noise have the exact manuscript normalization.
The generic sphere-preservation argument below specializes the proof from
`SphericalAging.CutoffSphere`; its sphere property is a proved conclusion.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SlowEquilibration.SphericalDynamics
open SphericalAging SphericalModel
open HardSphereDynamics LocalSDE VectorIto SpherePreservation StoppedVectorIto
open ClosedHitStopping StoppedSDE RadialItoRepresentation WeightedDriftSums CutoffSphere
set_option maxHeartbeats 2200000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Compact cutoff of the actual arbitrary smooth-gradient drift. -/
def cutoffDrift (β : ℝ) (g : State N → State N) (R : ℝ) (hR : 0 < R)
    (i : Fin N) (x : State N) : ℝ := (cutoffCoefficient R hR (drift β g) x) i

/-- Global Lipschitz bounds are proved from the compact smooth cutoff. -/
theorem cutoffDrift_lipschitz (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ ⊤ g) (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ≥0, ∀ i, LipschitzWith K (cutoffDrift β g R hR i) := by
  obtain ⟨K, hK⟩ := cutoffCoefficient_lipschitz R hR (drift β g)
    ((contDiff_drift β g hg).of_le (by simp))
  refine ⟨K, fun i => ?_⟩
  change LipschitzWith K (fun x => (cutoffCoefficient R hR (drift β g) x) i)
  simpa only [one_mul, Function.comp_def] using (CutoffSDE.coordinate_lipschitz i).comp hK

theorem cutoffDrift_eq (β : ℝ) (g : State N → State N) (R : ℝ) (hR : 0 < R)
    (x : State N) (hx : ‖x‖ ≤ R) (i : Fin N) :
    cutoffDrift β g R hR i x = drift β g x i := by
  simp only [cutoffDrift, cutoffCoefficient_eq R hR _ x hx]

omit [MeasurableSpace Ω] in
lemma stopped_physical_drift_cutoff (β : ℝ) (g : State N → State N) (_hg : ContDiff ℝ ⊤ g) (R : ℝ≥0)
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
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ ⊤ g) (R : ℝ≥0) (hR : 0 < (R : ℝ))
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
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ ⊤ g) (R : ℝ≥0) (hR : 0 < (R : ℝ))
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
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ ⊤ g) (R : ℝ≥0) (hR : 0 < (R : ℝ))
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



/-- Canonical cutoff radius strictly containing the manuscript's sphere. -/
def cutoffRadius (N : ℕ) : ℝ≥0 := N + 1

theorem cutoffRadius_pos (N : ℕ) : 0 < (cutoffRadius N : ℝ) := by
  simp only [cutoffRadius, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  positivity

theorem cutoffRadius_contains_sphere (N : ℕ) : (N : ℝ) < (cutoffRadius N : ℝ) ^ 2 := by
  simp only [cutoffRadius, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  nlinarith [sq_nonneg (N : ℝ), Nat.cast_nonneg (α := ℝ) N]

/-- The Euclidean gradient of the actual canonical mixed Gaussian field. -/
def mixedGradient (μ : FiniteMixture) (J : Disorder N μ.maxDegree) : State N → State N :=
  gradient (fieldOfMixture μ J)

theorem mixedGradient_contDiff (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    ContDiff ℝ ⊤ (mixedGradient μ J) := by
  unfold mixedGradient gradient
  exact ((InnerProductSpace.toDual ℝ (State N)).symm.contDiff).comp
    ((fieldOfMixture_contDiff μ J).fderiv_right (by simp))

/-- Literal manuscript drift, including the curvature correction. -/
def mixedDrift (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) : State N → State N :=
  drift β (mixedGradient μ J)

theorem mixedDrift_formula (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) :
    mixedDrift μ J β x = β • projection x (gradient (fieldOfMixture μ J) x) -
      (1 - 1 / (N : ℝ)) • x := by
  have hk : kappa N = 1 - 1 / (N : ℝ) := by
    unfold kappa
    field_simp
  simp only [mixedDrift, drift, mixedGradient, hk]

/-- A finite-horizon Picard solution of an arbitrary smooth projected drift
stays on the sphere. Its invariance is derived from the generic radial Ito
argument, with all-path modifications supplied by null augmentation. -/
theorem horizonProcess_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ ⊤ g)
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

/-- Canonical genuine Brownian-path cutoff solution for the actual mixture. -/
def mixedProcess (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (x : State N) : ℝ≥0 → VectorBrownian.Space N → State N :=
  GlobalSDE.process (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x

/-- Sphere preservation on one common event for every nonnegative time. -/
theorem mixedProcess_onSphere (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x) :
    ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, OnSphere (mixedProcess μ J β x t ω) := by
  have hall := ae_all_iff.mpr (fun n : ℕ => horizonProcess_onSphere hN
    (VectorBrownian.driver N) β (mixedGradient μ J) (mixedGradient_contDiff μ J)
    (cutoffRadius N) (cutoffRadius_pos N) (cutoffRadius_contains_sphere N) x hx
    (GlobalSDE.integerHorizon n)
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec)
  filter_upwards [hall] with ω hω
  intro t
  exact hω (Nat.ceil t) t (GlobalSDE.le_integerHorizon_ceil t)

/-- The constructed process satisfies the actual untruncated mixed Langevin
SDE, with real time integrals and the genuine independent coordinate Ito
integrals. No sphere-support or generator premise is assumed. -/
theorem mixedProcess_physical (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    IsLocalStrongSolutionOn (fun i z => mixedDrift μ J β z i)
      (fun i j z => noiseColumn z j i) physical_noise_continuous
      (NullAugmentation.driver (VectorBrownian.driver N)) x (mixedProcess μ J β x) T := by
  have hbound : ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, ‖mixedProcess μ J β x t ω‖ ≤ cutoffRadius N := by
    filter_upwards [mixedProcess_onSphere hN μ J β x hx] with ω hω
    intro t
    have hsq := (onSphere_iff_norm_sq _).mp (hω t)
    nlinarith [norm_nonneg (mixedProcess μ J β x t ω), (cutoffRadius N).coe_nonneg,
      cutoffRadius_contains_sphere N]
  have hcut := GlobalSDE.process_strongSolution
    (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x T
  exact coefficient_congr_onPath physical_noise_continuous hcut
    (fun i => hbound.mono (fun ω h t _ =>
      (cutoffDrift_eq β (mixedGradient μ J) _ (cutoffRadius_pos N) _ (h t) i).symm))
    (fun i j => hbound.mono (fun ω h t _ =>
      (CutoffSDE.cutoffNoise_eq N _ (cutoffRadius_pos N) _ (h t) i j).symm))

/-- Actual continuous paths for every initial state, without a form-domain premise. -/
theorem mixedProcess_continuous (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : State N) :
    ∀ᵐ ω ∂VectorBrownian.law N, Continuous (fun t => mixedProcess μ J β x t ω) :=
  GlobalSDE.process_continuous _ _ _ x

theorem mixedProcess_measurable (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : State N) (t : ℝ≥0) : Measurable (mixedProcess μ J β x t) :=
  ((GlobalSDE.process_stronglyAdapted _ _ _ x t).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le t)).measurable

/-- Probability law of the actual terminal mixed Langevin state. -/
def mixedTransitionLaw (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (x : State N) : Measure (State N) :=
  (VectorBrownian.law N).map (mixedProcess μ J β x t)

instance mixedTransitionLaw_probability (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (x : State N) :
    IsProbabilityMeasure (mixedTransitionLaw μ J β t x) := by
  unfold mixedTransitionLaw
  infer_instance

theorem mixedProcess_zero (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : State N) :
    mixedProcess μ J β x 0 =ᵐ[VectorBrownian.law N] fun _ => x :=
  (GlobalSDE.process_strongSolution
    (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x 0).initial

/-- Zero time is the actual point-mass kernel law. -/
theorem mixedTransitionLaw_zero (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : State N) : mixedTransitionLaw μ J β 0 x = Measure.dirac x := by
  rw [mixedTransitionLaw, Measure.map_congr (mixedProcess_zero μ J β x),
    Measure.map_const, measure_univ, one_smul]

theorem sphere_measurableSet (N : ℕ) : MeasurableSet {x : State N | OnSphere x} := by
  simpa only [OnSphere, real_inner_self_eq_norm_sq, Pi.pow_apply, id_eq] using
    (isClosed_eq (continuous_id.norm.pow 2) (continuous_const (y := (N : ℝ)))).measurableSet

/-- Every physical initial state has a transition probability fully supported
on the radius-`sqrt N` sphere, for every nonnegative time. -/
theorem mixedTransitionLaw_support (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    mixedTransitionLaw μ J β t x {y : State N | OnSphere y} = 1 := by
  rw [mixedTransitionLaw, Measure.map_apply (mixedProcess_measurable μ J β x t)
    (sphere_measurableSet N)]
  calc
    _ = (VectorBrownian.law N) Set.univ := by
      apply measure_congr
      filter_upwards [mixedProcess_onSphere hN μ J β x hx] with ω hω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ]
      simp [hω t]
    _ = 1 := measure_univ


/-! The fixed-coefficient Picard layer is genuinely generic. Its initial-state
measurability is proved here, rather than assumed as a transition-kernel axiom. -/
namespace FixedCoefficients
open PredictableItoTime PredictableDriftTime PredictableTerminalOperators JointAdaptedContinuous
open FourPapersCommon.FilteredBrownian

variable (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
  (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j))

def process (T : ℝ≥0) (x : State N) : ℝ≥0 → Ω → State N :=
  GlobalSDE.horizonProcess D hb hs x T

def driftClass (T : ℝ≥0) (i : Fin N) (x : State N) : PredictableProcessL2 F P :=
  predictableCoefficient (hb i) (GlobalSDE.horizonClass D hb hs x T) T

def noiseClass (T : ℝ≥0) (i j : Fin N) (x : State N) : PredictableProcessL2 F P :=
  predictableCoefficient (hs i j) (GlobalSDE.horizonClass D hb hs x T) T

theorem coefficientClass_continuous (T : ℝ≥0) {K : ℝ≥0}
    (g : State N → ℝ) (hg : LipschitzWith K g) :
    Continuous (fun x : State N =>
      predictableCoefficient hg (GlobalSDE.horizonClass D hb hs x T) T) := by
  have hcoef : LipschitzWith K
      (fun U : PredictableStateL2 N F P => predictableCoefficient hg U T) := by
    apply LipschitzWith.of_dist_le_mul
    intro U V
    simpa only [dist_eq_norm] using norm_predictableCoefficient_sub_le hg U V T
  exact hcoef.continuous.comp
    (PicardDependence.horizonClass_lipschitz_initial D hb hs T).choose_spec.continuous

theorem driftClass_continuous (T : ℝ≥0) (i : Fin N) :
    Continuous (driftClass D hb hs T i) := coefficientClass_continuous D hb hs T _ (hb i)

theorem noiseClass_continuous (T : ℝ≥0) (i j : Fin N) :
    Continuous (noiseClass D hb hs T i j) := coefficientClass_continuous D hb hs T _ (hs i j)

def scalarClass (T t : ℝ≥0) (i : Fin N) (x : State N) : lpMeas ℝ ℝ (F t) 2 P :=
  initialTerminal t (x i) + driftTerminalAdapted T t (driftClass D hb hs T i x) +
    ∑ j : Fin N, naturalItoProcessLpMeas (D.filtered j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) (noiseClass D hb hs T i j x) t

theorem scalarClass_continuous (T t : ℝ≥0) (i : Fin N) :
    Continuous (scalarClass D hb hs T t i) := by
  apply Continuous.add
  · apply Continuous.add
    · apply (initialTerminal_lipschitz t).continuous.comp
      fun_prop
    · exact (driftTerminalAdapted_lipschitz T t).continuous.comp (driftClass_continuous D hb hs T i)
  · exact continuous_finsetSum Finset.univ (fun j _ =>
      (itoTerminalAdapted_lipschitz D j t).continuous.comp (noiseClass_continuous D hb hs T i j))

def stateClass (T t : ℝ≥0) (x : State N) : lpMeas (State N) ℝ (F t) 2 P :=
  ∑ i : Fin N, scalarToStateTerminal t i (scalarClass D hb hs T t i x)

theorem stateClass_continuous (T t : ℝ≥0) : Continuous (stateClass D hb hs T t) :=
  continuous_finsetSum Finset.univ (fun i _ =>
    (scalarToStateTerminal_continuous t i).comp (scalarClass_continuous D hb hs T t i))

lemma scalarClass_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j)) (T t : ℝ≥0)
    (i : Fin N) (q : State N) :
    (scalarClass D hb hs T t i q : Lp ℝ 2 P) =ᵐ[P]
      coordinateVersion D
        hb
        hs q T (GlobalSDE.horizonClass D hb hs q T) i t := by
  let A := initialTerminal (F := F) (P := P) t (q i)
  let B := driftTerminalAdapted (F := F) (P := P) T t (driftClass D hb hs T i q)
  let C := fun j : Fin N => naturalItoProcessLpMeas (D.filtered j).toIsPreBrownianReal
    (D.coordinateStronglyMeasurable j) (D.filtered j) (noiseClass D hb hs T i j q) t
  have hsum : ((∑ j, C j : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P) =ᵐ[P]
      (fun ω => ∑ j, (C j : RandomL2 P) ω) := by
    simpa only [Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ (fun j => (C j : RandomL2 P))
  have hi : ∀ᵐ ω ∂P, ∀ j : Fin N, (C j : RandomL2 P) ω=
      SphericalAging.PredictableItoTime.itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) (noiseClass D hb hs T i j q) t ω :=
    ae_all_iff.mpr (fun j => SphericalAging.PredictableItoTime.itoVersion_ae_eq
      (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) _ t)
  filter_upwards [Lp.coeFn_add ((A+B : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P)
      ((∑ j, C j : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P),
    Lp.coeFn_add (A : RandomL2 P) (B : RandomL2 P),
    Lp.coeFn_const 2 P (q i),
    (SphericalAging.PredictableDriftTime.driftVersion_memLp (driftClass D hb hs T i q) T t).coeFn_toLp,
    hsum,hi] with ω hadd hab ha hcoefdrift hc hnoise
  change (((A+B+(∑ j, C j) : lpMeas ℝ ℝ (F t) 2 P)) : RandomL2 P) ω = _
  simp only [Submodule.coe_add] at hadd hab ⊢
  rw [hadd,Pi.add_apply,hab,Pi.add_apply]
  change ((Lp.const 2 P) (q i) : Ω → ℝ) ω+
    (((SphericalAging.PredictableDriftTime.driftVersion_memLp (driftClass D hb hs T i q) T t).toLp _) : Ω → ℝ) ω+
      ((∑ j, C j : lpMeas ℝ ℝ (F t) 2 P) : RandomL2 P) ω = _
  rw [ha,hcoefdrift,hc]
  simp only [hnoise]
  rfl

lemma stateClass_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i, LipschitzWith Kb (b i)) (hs : ∀ i j, LipschitzWith Ks (sigma i j)) (T t : ℝ≥0)
    (q : State N) :
    (stateClass D hb hs T t q : Lp (State N) 2 P) =ᵐ[P] process D hb hs T q t := by
  have hsumState : (stateClass D hb hs T t q : Lp (State N) 2 P) =ᵐ[P]
      (fun ω => ∑ i, (scalarToStateTerminal t i (scalarClass D hb hs T t i q) : Lp (State N) 2 P) ω) := by
    simpa only [stateClass,Submodule.coe_sum] using Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (scalarToStateTerminal t i (scalarClass D hb hs T t i q) : Lp (State N) 2 P))
  have hi : ∀ᵐ ω ∂P, ∀ i : Fin N,
      (scalarToStateTerminal t i (scalarClass D hb hs T t i q) : Lp (State N) 2 P) ω =
        (scalarClass D hb hs T t i q : Lp ℝ 2 P) ω • basisVector i :=
    ae_all_iff.mpr (fun i => (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLp _)
  have hsc := ae_all_iff.mpr (fun i => scalarClass_ae D hb hs T t i q)
  filter_upwards [hsumState,hi,hsc] with ω hsumState hi hsc
  rw [hsumState]
  simp only [hi,hsc]
  rfl


/-- Constructed jointly adapted and jointly measurable all-time solution
family for arbitrary globally Lipschitz fixed coefficients. -/
theorem exists_joint_adapted_global_process :
    ∃ Y : State N → ℝ≥0 → Ω → State N,
      StronglyMeasurable (fun q : State N × (ℝ≥0 × Ω) => Y q.1 q.2.1 q.2.2) ∧
      (∀ t, StronglyMeasurable[(inferInstance : MeasurableSpace (State N)).prod (F t)]
        (fun q : State N × Ω => Y q.1 t q.2)) ∧
      ∀ x, ∀ᵐ ω ∂P,
        (∀ t, Y x t ω = GlobalSDE.process D hb hs x t ω) ∧
          Continuous (fun t => Y x t ω) := by
  apply exists_jointAdapted_continuous_version
    (fun t => stateClass D hb hs (GlobalSDE.integerHorizon (Nat.ceil t)) t)
    (fun t => (stateClass_continuous D hb hs _ t).stronglyMeasurable)
    (GlobalSDE.process D hb hs) (GlobalSDE.process_continuous D hb hs)
  intro x t
  exact stateClass_ae D hb hs _ t x

/-- A canonical actual joint solution family, identified with the Picard
solution at every time on each initial-state slice. -/
def jointProcess : State N → ℝ≥0 → Ω → State N :=
  (exists_joint_adapted_global_process D hb hs).choose

theorem jointProcess_measurable :
    StronglyMeasurable (fun q : State N × (ℝ≥0 × Ω) =>
      jointProcess D hb hs q.1 q.2.1 q.2.2) :=
  (exists_joint_adapted_global_process D hb hs).choose_spec.1

theorem jointProcess_adapted (t : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace (State N)).prod (F t)]
      (fun q : State N × Ω => jointProcess D hb hs q.1 t q.2) :=
  (exists_joint_adapted_global_process D hb hs).choose_spec.2.1 t

theorem jointProcess_ae (x : State N) : ∀ᵐ ω ∂P,
    ∀ t, jointProcess D hb hs x t ω = GlobalSDE.process D hb hs x t ω :=
  ((exists_joint_adapted_global_process D hb hs).choose_spec.2.2 x).mono (fun _ h => h.1)

theorem terminal_measurable (t : ℝ≥0) :
    Measurable (fun q : State N × Ω => jointProcess D hb hs q.1 t q.2) :=
  (jointProcess_measurable D hb hs).measurable.comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- Actual joint-family transition probabilities. -/
def transitionKernel (t : ℝ≥0) : Kernel (State N) (State N) :=
  (Kernel.id ×ₖ Kernel.const (State N) P).map
    (fun q : State N × Ω => jointProcess D hb hs q.1 t q.2)

instance transitionKernel_markov (t : ℝ≥0) : IsMarkovKernel (transitionKernel D hb hs t) :=
  Kernel.IsMarkovKernel.map _ (terminal_measurable D hb hs t)

theorem transitionKernel_apply (t : ℝ≥0) (x : State N) :
    transitionKernel D hb hs t x = P.map (fun ω => GlobalSDE.process D hb hs x t ω) := by
  rw [transitionKernel, Kernel.map_apply _ (terminal_measurable D hb hs t),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (terminal_measurable D hb hs t) measurable_prodMk_left]
  exact Measure.map_congr ((jointProcess_ae D hb hs x).mono (fun _ h => h t))


/-- Ordinary global coefficient bounds for the compact-cutoff SDE. -/
structure CoefficientBounds (b : Fin N → State N → ℝ)
    (sigma : Fin N → Fin N → State N → ℝ) where
  driftBound : ℝ≥0
  noiseBound : ℝ≥0
  drift_bound : ∀ i x, ‖b i x‖ ≤ driftBound
  noise_bound : ∀ i j x, ‖sigma i j x‖ ≤ noiseBound

namespace ProductFamily
open IndependentBackgroundDriver ParameterizedItoLift ParameterizedItoVersion ParameterizedDriftLift
open AnnealedCutoffCoefficients AnnealedSDECore HamiltonianFamilyIntegrability
variable {ρ : Measure (State N)} [IsProbabilityMeasure ρ]
variable (B : CoefficientBounds b sigma)
include B

theorem driftClass_memLp (T : ℝ≥0) (i : Fin N) :
    MemLp (FixedCoefficients.driftClass D hb hs T i) 2 ρ := by
  apply (memLp_const ((B.driftBound : ℝ) * (PicardDependence.initialScale (P := P) T : ℝ))).of_le
    (FixedCoefficients.driftClass_continuous D hb hs T i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_predictableCoefficient_le_of_bound (hb i)
    (GlobalSDE.horizonClass D hb hs x T) T _ B.driftBound.coe_nonneg (B.drift_bound i)

theorem noiseClass_memLp (T : ℝ≥0) (i j : Fin N) :
    MemLp (FixedCoefficients.noiseClass D hb hs T i j) 2 ρ := by
  apply (memLp_const ((B.noiseBound : ℝ) * (PicardDependence.initialScale (P := P) T : ℝ))).of_le
    (FixedCoefficients.noiseClass_continuous D hb hs T i j).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_predictableCoefficient_le_of_bound (hs i j)
    (GlobalSDE.horizonClass D hb hs x T) T _ B.noiseBound.coe_nonneg (B.noise_bound i j)

/-- Actual outer L² class of the nonlinear drift coefficients. -/
def driftFamily 
     (T : ℝ≥0) (i : Fin N) :
    Lp (PredictableProcessL2 F P) 2 ρ :=
  (driftClass_memLp (ρ := ρ) D hb hs B T i).toLp (FixedCoefficients.driftClass D hb hs T i)

/-- Actual outer L² class of the nonlinear matrix-noise coefficients. -/
def noiseFamily 
    (T : ℝ≥0) (i j : Fin N) : Lp (PredictableProcessL2 F P) 2 ρ :=
  (noiseClass_memLp (ρ := ρ) D hb hs B T i j).toLp (FixedCoefficients.noiseClass D hb hs T i j)

def driftLift 
     (T : ℝ≥0) (i : Fin N) :
    PredictableProcessL2 (filtration (State N) F) (ρ.prod P) :=
  PredictableFamilyLift.familyLift (driftFamily (ρ := ρ) D hb hs B T i)

def noiseLift 
    (T : ℝ≥0) (i j : Fin N) :
    PredictableProcessL2 (filtration (State N) F) (ρ.prod P) :=
  PredictableFamilyLift.familyLift (noiseFamily (ρ := ρ) D hb hs B T i j)

/-- The genuine enlarged-filtration continuous scalar integral version. -/
def coordinateProcess 
     (T : ℝ≥0) (i : Fin N)
    (t : ℝ≥0) (ω : State N × Ω) : ℝ :=
  ω.1 i + driftVersion (driftLift (ρ := ρ) D hb hs B T i) T t ω +
    ∑ j : Fin N, itoVersion ((driver (ρ := ρ) D).brownian j)
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j)
      (noiseLift (ρ := ρ) D hb hs B T i j) t ω

/-- Actual state-valued annealed cutoff process on a finite horizon. -/
def process 
     (T : ℝ≥0)
    (t : ℝ≥0) (ω : State N × Ω) : State N :=
  ∑ i : Fin N, coordinateProcess (ρ := ρ) D hb hs B T i t ω • basisVector i

lemma coordinateProcess_stronglyAdapted 
     (T : ℝ≥0) (i : Fin N) :
    StronglyAdapted (filtration (State N) F) (coordinateProcess (ρ := ρ) D hb hs B T i) := by
  intro t
  apply StronglyMeasurable.add
  · apply StronglyMeasurable.add
    · exact ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).stronglyMeasurable.comp_measurable
        (background_known t))
    · exact driftVersion_stronglyAdapted _ T t
  · exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ =>
      itoVersion_stronglyAdapted ((driver (ρ := ρ) D).brownian j)
        ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j) _ t)

lemma process_stronglyAdapted 
     (T : ℝ≥0) :
    StronglyAdapted (filtration (State N) F) (process (ρ := ρ) D hb hs B T) := by
  intro t
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (coordinateProcess_stronglyAdapted (ρ := ρ) D hb hs B T i t).smul_const (basisVector i))

lemma coordinateProcess_continuous 
     (T : ℝ≥0) (i : Fin N) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => coordinateProcess (ρ := ρ) D hb hs B T i t ω) := by
  have hall : ∀ᵐ ω ∂ρ.prod P, ∀ j : Fin N, Continuous (fun t => itoVersion
      ((driver (ρ := ρ) D).brownian j) ((driver (ρ := ρ) D).coordinateStronglyMeasurable j)
      ((driver (ρ := ρ) D).filtered j) (noiseLift (ρ := ρ) D hb hs B T i j) t ω) :=
    ae_all_iff.mpr (fun j => (itoVersion_continuousModification ((driver (ρ := ρ) D).brownian j)
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j) _).continuous_paths)
  filter_upwards [driftVersion_ae_continuous (driftLift (ρ := ρ) D hb hs B T i) T,hall] with ω hd hn
  exact (continuous_const.add hd).add (continuous_finsetSum Finset.univ (fun j _ => hn j))

lemma process_continuous 
     (T : ℝ≥0) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => process (ρ := ρ) D hb hs B T t ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => coordinateProcess_continuous (ρ := ρ) D hb hs B T i)] with ω hc
  exact continuous_finsetSum Finset.univ (fun i _ => (hc i).smul continuous_const)

lemma coordinateProcess_slice 
     (T t : ℝ≥0) (i : Fin N) :
    ∀ᵐ q ∂ρ, (fun ω => coordinateProcess (ρ := ρ) D hb hs B T i t (q,ω)) =ᵐ[P]
      coordinateVersion D hb
        hs q T (GlobalSDE.horizonClass D hb hs q T) i t := by
  have hd := ParameterizedDriftLift.driftVersion_familyLift T (driftFamily (ρ := ρ) D hb hs B T i)
  have hn : ∀ᵐ q ∂ρ, ∀ j : Fin N,
      (fun ω => itoVersion ((driver (ρ := ρ) D).brownian j)
        ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j)
        (noiseLift (ρ := ρ) D hb hs B T i j) t (q,ω)) =ᵐ[P]
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (noiseFamily (ρ := ρ) D hb hs B T i j q) t :=
    ae_all_iff.mpr (fun j => ParameterizedItoVersion.itoVersion_familyLift_slice D j (noiseFamily (ρ := ρ) D hb hs B T i j) t)
  have hnf : ∀ᵐ q ∂ρ, ∀ j : Fin N,
      noiseFamily (ρ := ρ) D hb hs B T i j q = FixedCoefficients.noiseClass D hb hs T i j q :=
    ae_all_iff.mpr (fun j => (noiseClass_memLp (ρ := ρ) D hb hs B T i j).coeFn_toLp)
  filter_upwards [hd,hn,hnf,(driftClass_memLp (ρ := ρ) D hb hs B T i).coeFn_toLp] with q hd hn hnf hdf
  have hna := ae_all_iff.mpr hn
  filter_upwards [hd,hna] with ω hd hn
  have hd' : driftVersion (driftLift (ρ := ρ) D hb hs B T i) T t (q,ω) =
      driftVersion (FixedCoefficients.driftClass D hb hs T i q) T t ω :=
    (hd t).trans (congrArg (fun U => driftVersion U T t ω) hdf)
  have hn' (j : Fin N) : itoVersion ((driver (ρ := ρ) D).brownian j)
      ((driver (ρ := ρ) D).coordinateStronglyMeasurable j) ((driver (ρ := ρ) D).filtered j)
      (noiseLift (ρ := ρ) D hb hs B T i j) t (q,ω) =
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (FixedCoefficients.noiseClass D hb hs T i j q) t ω :=
    (hn j).trans (congrArg (fun U => itoVersion (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) U t ω) (hnf j))
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl hd')
    (Finset.sum_congr rfl (fun j _ => hn' j))

/-- At every terminal time the actual product process has the genuine
deterministic-parameter Hamiltonian solution as its parameter sections. -/
theorem process_slice 
     (T t : ℝ≥0) :
    ∀ᵐ q ∂ρ, (fun ω => process (ρ := ρ) D hb hs B T t (q,ω)) =ᵐ[P]
      FixedCoefficients.process D hb hs T q t := by
  filter_upwards [ae_all_iff.mpr (fun i => coordinateProcess_slice (ρ := ρ) D hb hs B T t i)] with q hq
  filter_upwards [ae_all_iff.mpr hq] with ω hω
  unfold process FixedCoefficients.process GlobalSDE.horizonProcess version
  simp only [hω]

/-- On almost every parameter section, one common path event identifies
the actual product process and the genuine canonical solution at all times. -/
theorem process_slice_allTimes 
     (T : ℝ≥0) :
    ∀ᵐ q ∂ρ, ∀ᵐ ω ∂P, ∀ t, process (ρ := ρ) D hb hs B T t (q,ω) =
      FixedCoefficients.process D hb hs T q t ω := by
  have hg : ∀ᵐ q ∂ρ, ∀ n k : ℕ,
      (fun ω => process (ρ := ρ) D hb hs B T (AdaptedContinuous.gridTime n k) (q,ω)) =ᵐ[P]
      FixedCoefficients.process D hb hs T q (AdaptedContinuous.gridTime n k) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => process_slice (ρ := ρ) D hb hs B T _))
  filter_upwards [hg,Measure.ae_ae_of_ae_prod (process_continuous (ρ := ρ) D hb hs B T)] with q hg hc
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hg n)),hc,
    GlobalSDE.horizonProcess_continuous D hb hs q T] with ω hg hx hy
  intro t
  have he : (fun n => process (ρ := ρ) D hb hs B T (AdaptedContinuous.pastGrid t n) (q,ω)) =
      (fun n => FixedCoefficients.process D hb hs T q (AdaptedContinuous.pastGrid t n) ω) :=
    funext (fun n => hg n _)
  have hxlim := (hx.tendsto t).comp (AdaptedContinuous.tendsto_pastGrid t)
  simp only [Function.comp_def] at hxlim
  rw [he] at hxlim
  exact tendsto_nhds_unique hxlim ((hy.tendsto t).comp (AdaptedContinuous.tendsto_pastGrid t))

/-- The genuine all-time canonical parameter solution agrees with the
actual annealed finite-horizon process throughout its physical horizon. -/
theorem process_slice_global 
     (T : ℝ≥0) :
    ∀ᵐ q ∂ρ, ∀ᵐ ω ∂P, ∀ t, t ≤ T → process (ρ := ρ) D hb hs B T t (q,ω) =
      GlobalSDE.process D hb hs q t ω := by
  filter_upwards [process_slice_allTimes (ρ := ρ) D hb hs B T] with q hq
  have hglobal := GlobalSDE.process_eq_horizon D
    hb
    hs q T
  filter_upwards [hq,hglobal] with ω hq hglobal
  intro t ht
  exact (hq t).trans (hglobal t ht).symm


/-- Actual evaluated drift and diffusion coefficients on the product family. -/
def driftProcess (T : ℝ≥0) (i : Fin N) (t : ℝ≥0) (ω : State N × Ω) : ℝ :=
  b i (process (ρ := ρ) D hb hs B T t ω)

def noiseProcess (T : ℝ≥0) (i j : Fin N) (t : ℝ≥0) (ω : State N × Ω) : ℝ :=
  sigma i j (process (ρ := ρ) D hb hs B T t ω)

theorem driftProcess_stronglyAdapted (T : ℝ≥0) (i : Fin N) :
    StronglyAdapted (filtration (State N) F) (driftProcess (ρ := ρ) D hb hs B T i) :=
  fun t => (hb i).continuous.comp_stronglyMeasurable (process_stronglyAdapted (ρ := ρ) D hb hs B T t)

theorem driftProcess_continuous (T : ℝ≥0) (i : Fin N) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => driftProcess (ρ := ρ) D hb hs B T i t ω) :=
  (process_continuous (ρ := ρ) D hb hs B T).mono (fun _ h => (hb i).continuous.comp h)

theorem noiseProcess_stronglyAdapted (T : ℝ≥0) (i j : Fin N) :
    StronglyAdapted (filtration (State N) F) (noiseProcess (ρ := ρ) D hb hs B T i j) :=
  fun t => (hs i j).continuous.comp_stronglyMeasurable (process_stronglyAdapted (ρ := ρ) D hb hs B T t)

theorem noiseProcess_continuous (T : ℝ≥0) (i j : Fin N) :
    ∀ᵐ ω ∂ρ.prod P, Continuous (fun t => noiseProcess (ρ := ρ) D hb hs B T i j t ω) :=
  (process_continuous (ρ := ρ) D hb hs B T).mono (fun _ h => (hs i j).continuous.comp h)

/-- Actual enlarged drift class equals evaluation of the random-disorder
cutoff drift on the constructed process. -/
theorem driftLift_coe 
     (T : ℝ≥0) (i : Fin N) :
    (driftLift (ρ := ρ) D hb hs B T i : TimeProcessL2 (ρ.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      FourPapersCommon.continuousAdaptedTimeCut (driftProcess (ρ := ρ) D hb hs B T i) T := by
  let V := driftLift (ρ := ρ) D hb hs B T i
  let H := FourPapersCommon.continuousAdaptedTimeCut (driftProcess (ρ := ρ) D hb hs B T i) T
  have hHa : AEStronglyMeasurable H (nonnegativeLebesgueMeasure.prod (ρ.prod P)) :=
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut (filtration (State N) F) _
      (driftProcess_stronglyAdapted (ρ := ρ) D hb hs B T i) (driftProcess_continuous (ρ := ρ) D hb hs B T i) T).mono
        (predictable_le_prod _)
  have he : (fun z : State N × (ℝ≥0 × Ω) => (V : TimeProcessL2 (ρ.prod P))
      (ParameterizedItoLift.unshuffle z)) =ᵐ[ρ.prod (nonnegativeLebesgueMeasure.prod P)]
      H ∘ ParameterizedItoLift.unshuffle := by
    apply ae_eq_of_ae_sections
      ((Lp.aestronglyMeasurable (V : TimeProcessL2 (ρ.prod P))).comp_quasiMeasurePreserving
        (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
      (hHa.comp_quasiMeasurePreserving (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
    filter_upwards [ParameterizedItoLift.predictableFamily_slice_ae (driftFamily (ρ := ρ) D hb hs B T i),
      (driftClass_memLp (ρ := ρ) D hb hs B T i).coeFn_toLp,process_slice_allTimes (ρ := ρ) D hb hs B T] with q hv hf hx
    have hcan := predictableCoefficient_ae_actual
      (hb i) T
      (GlobalSDE.horizonProcess_timeCut D
        hb
        hs q T)
    have hxt := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hx
    filter_upwards [hv,hcan,hxt] with z hv hcan hx
    have hv' : (V : TimeProcessL2 (ρ.prod P)) (z.1,(q,z.2)) =
        (FixedCoefficients.driftClass D hb hs T i q : TimeProcessL2 P) z :=
      hv.trans (congrArg (fun U : PredictableProcessL2 F P => (U : TimeProcessL2 P) z) hf)
    exact hv'.trans (hcan.trans (by
      simp only [H,driftProcess,ParameterizedItoLift.unshuffle,Function.comp_def,
        FourPapersCommon.continuousAdaptedTimeCut,hx z.1]
      rfl))
  have hb := (PredictableFamilyLift.shuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp he
  exact hb

/-- Actual enlarged matrix-noise class equals evaluation of the cutoff
projection coefficient on the constructed annealed process. -/
theorem noiseLift_coe 
     (T : ℝ≥0) (i j : Fin N) :
    (noiseLift (ρ := ρ) D hb hs B T i j : TimeProcessL2 (ρ.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod (ρ.prod P)]
      FourPapersCommon.continuousAdaptedTimeCut (noiseProcess (ρ := ρ) D hb hs B T i j) T := by
  let V := noiseLift (ρ := ρ) D hb hs B T i j
  let H := FourPapersCommon.continuousAdaptedTimeCut (noiseProcess (ρ := ρ) D hb hs B T i j) T
  have hHa : AEStronglyMeasurable H (nonnegativeLebesgueMeasure.prod (ρ.prod P)) :=
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut (filtration (State N) F) _
      (noiseProcess_stronglyAdapted (ρ := ρ) D hb hs B T i j) (noiseProcess_continuous (ρ := ρ) D hb hs B T i j) T).mono
        (predictable_le_prod _)
  have he : (fun z : State N × (ℝ≥0 × Ω) => (V : TimeProcessL2 (ρ.prod P))
      (ParameterizedItoLift.unshuffle z)) =ᵐ[ρ.prod (nonnegativeLebesgueMeasure.prod P)]
      H ∘ ParameterizedItoLift.unshuffle := by
    apply ae_eq_of_ae_sections
      ((Lp.aestronglyMeasurable (V : TimeProcessL2 (ρ.prod P))).comp_quasiMeasurePreserving
        (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
      (hHa.comp_quasiMeasurePreserving (ParameterizedItoLift.unshuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving)
    filter_upwards [ParameterizedItoLift.predictableFamily_slice_ae (noiseFamily (ρ := ρ) D hb hs B T i j),
      (noiseClass_memLp (ρ := ρ) D hb hs B T i j).coeFn_toLp,process_slice_allTimes (ρ := ρ) D hb hs B T] with q hv hf hx
    have hcan := predictableCoefficient_ae_actual
      (hs i j) T
      (GlobalSDE.horizonProcess_timeCut D
        hb
        hs q T)
    have hxt := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hx
    filter_upwards [hv,hcan,hxt] with z hv hcan hx
    have hv' : (V : TimeProcessL2 (ρ.prod P)) (z.1,(q,z.2)) =
        (FixedCoefficients.noiseClass D hb hs T i j q : TimeProcessL2 P) z :=
      hv.trans (congrArg (fun U : PredictableProcessL2 F P => (U : TimeProcessL2 P) z) hf)
    exact hv'.trans (hcan.trans (by
      simp only [H,noiseProcess,ParameterizedItoLift.unshuffle,Function.comp_def,
        FourPapersCommon.continuousAdaptedTimeCut,hx z.1]
      rfl))
  have hb := (PredictableFamilyLift.shuffle_measurePreserving (ρ := ρ) (P := P)).quasiMeasurePreserving.ae_eq_comp he
  exact hb


theorem process_apply (T t : ℝ≥0) (ω : State N × Ω) (i : Fin N) :
    process (ρ := ρ) D hb hs B T t ω i = coordinateProcess (ρ := ρ) D hb hs B T i t ω := by
  simp [process, basisVector, Pi.single_apply]

/-- The product-family process satisfies the literal random-initial SDE
with the actual independent-background stochastic integrals. -/
theorem process_strongSolution (T : ℝ≥0) :
    IsRandomStrongSolutionOn (driver (ρ := ρ) D)
      (fun _ => b) (fun _ => sigma) (fun ω => ω.1) (process (ρ := ρ) D hb hs B T) T := by
  refine ⟨(continuous_id : Continuous (id : State N → State N)).stronglyMeasurable.comp_measurable
    (background_known 0), process_stronglyAdapted (ρ := ρ) D hb hs B T, process_continuous (ρ := ρ) D hb hs B T,
    driftLift (ρ := ρ) D hb hs B T, (fun i j => noiseLift (ρ := ρ) D hb hs B T i j),
    (fun i => driftLift_coe (ρ := ρ) D hb hs B T i), (fun i j => noiseLift_coe (ρ := ρ) D hb hs B T i j), ?_⟩
  intro t ht i
  have hd := driftVersion_eq_actual (driftLift (ρ := ρ) D hb hs B T i)
    (driftProcess (ρ := ρ) D hb hs B T i) T (driftLift_coe (ρ := ρ) D hb hs B T i)
  have hn := vectorProcessLp_ae_itoVersions (driver (ρ := ρ) D)
    (fun j => noiseLift (ρ := ρ) D hb hs B T i j) t
  filter_upwards [hd, hn] with ω hd hn
  rw [process_apply]
  unfold coordinateProcess
  rw [hd t ht, hn]
  rfl

end ProductFamily


/-- Actual fixed-coefficient transition expectation. -/
def transition (t : ℝ≥0) (f : State N → ℝ) (x : State N) : ℝ :=
  ∫ ω, f (jointProcess D hb hs x t ω) ∂P

theorem transition_eq_actual (t : ℝ≥0) (f : State N → ℝ) (x : State N) :
    transition D hb hs t f x = ∫ ω, f (GlobalSDE.process D hb hs x t ω) ∂P := by
  apply integral_congr_ae
  exact (jointProcess_ae D hb hs x).mono (fun _ h => congrArg f (h t))

theorem transition_measurable (t : ℝ≥0) (f : State N → ℝ) (hf : Continuous f) :
    StronglyMeasurable (transition D hb hs t f) :=
  (hf.stronglyMeasurable.comp_measurable (terminal_measurable D hb hs t)).integral_prod_right'

theorem transition_eq_kernel_integral (t : ℝ≥0) (f : State N → ℝ)
    (hf : StronglyMeasurable f) (x : State N) :
    transition D hb hs t f x = ∫ y, f y ∂transitionKernel D hb hs t x := by
  rw [transition_eq_actual, transitionKernel_apply]
  exact (integral_map (((GlobalSDE.process_stronglyAdapted D hb hs x t).mono
    (F.le t)).aemeasurable) hf.aestronglyMeasurable).symm

/-- The canonical genuine independent vector Brownian driver with its
constructed null-augmented filtration. -/
def canonicalDriver (N : ℕ) : BrownianDriver N (VectorBrownian.law N)
    (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)) :=
  NullAugmentation.driver (VectorBrownian.driver N)

/-- The future of the actual cutoff solution is the constructed solution
family evaluated at the observed waiting state and the actual future Wiener
path. This is derived using product-law stochastic lifts and true uniqueness. -/
theorem future_restart (B : CoefficientBounds b sigma) (x : State N) (s t : ℝ≥0) :
    GlobalSDE.process (canonicalDriver N) hb hs x (s + t) =ᵐ[VectorBrownian.law N]
      fun ω => jointProcess (canonicalDriver N) hb hs
        (GlobalSDE.process (canonicalDriver N) hb hs x s ω) t (BrownianFuturePath.future s ω) := by
  let P0 := VectorBrownian.law N
  let F0 := NullAugmentation.augment (VectorBrownian.filtration N) P0
  let D0 := canonicalDriver N
  let X := GlobalSDE.process D0 hb hs x
  have hX (T : ℝ≥0) : AnnealedSDECore.IsRandomStrongSolutionOn D0
      (fun _ => b) (fun _ => sigma) (fun _ => x) X T :=
    RandomSDEConversions.localStrongSolution_to_random (fun i => (hb i).continuous)
      (GlobalSDE.process_strongSolution D0 hb hs x T)
  have hXa := GlobalSDE.process_stronglyAdapted D0 hb hs x
  have hZa : Measurable[F0 s] (X s) := (hXa s).measurable
  have hZm : Measurable (X s) := hZa.mono (F0.le s) le_rfl
  let ρ := P0.map (X s)
  let : IsProbabilityMeasure ρ := by dsimp [ρ, P0]; infer_instance
  let E := IndependentBackgroundDriver.driver (ρ := ρ) D0
  let Y := ProductFamily.process (ρ := ρ) D0 hb hs B t
  let φ : VectorBrownian.Space N → State N × VectorBrownian.Space N :=
    fun ω => (X s ω, BrownianFuturePath.future s ω)
  have hφ : MeasurePreserving φ P0 (ρ.prod P0) :=
    BrownianFutureFiltered.waiting_future_measurePreserving s (X s) hZa
  have hφF : ∀ u, @Measurable (VectorBrownian.Space N)
      (State N × VectorBrownian.Space N) (ShiftedBrownian.filtration F0 s u)
      (IndependentBackgroundDriver.filtration (State N) F0 u) φ :=
    BrownianFutureFiltered.waiting_future_filtered s (X s) hZa
  have hBrownian : ∀ i u, (ShiftedBrownian.driver D0 s).coordinate i u =ᵐ[P0]
      (fun ω => E.coordinate i u (φ ω)) := fun _ _ => .of_forall (fun _ => rfl)
  have hYpull : AnnealedSDECore.IsRandomStrongSolutionOn (ShiftedBrownian.driver D0 s)
      (fun _ => b) (fun _ => sigma) (X s) (fun u ω => Y u (φ ω)) t :=
    FilteredRandomSDEPullback.randomStrongSolution_pullback hφ hφF E
      (ShiftedBrownian.driver D0 s) hBrownian _ _ _ _ t
      (ProductFamily.process_strongSolution (ρ := ρ) D0 hb hs B t)
  have hXfuture := ShiftedRandomSDE.randomStrongSolution_timeShift D0
    (fun _ => b) (fun _ => sigma) (fun _ i => (hb i).continuous)
    (fun _ => x) X s t (hX (s + t))
  have hmem : MemLp (X s) 2 P0 :=
    RandomSDEStateClass.strongSolution_terminal_memLp D0 (fun _ => b) (fun _ => sigma)
      (fun _ => x) (memLp_const x) X s (hX s) s le_rfl
  have hsame := RandomSDEStateClass.randomStrongSolutions_unique
    (ShiftedBrownian.driver D0 s) hb hs (X s) hmem
    (ShiftedSDE.stateShift X s) (fun u ω => Y u (φ ω)) t hXfuture hYpull
  have hYjoint : Y t =ᵐ[ρ.prod P0]
      fun q => jointProcess D0 hb hs q.1 t q.2 := by
    have hmY := (ProductFamily.process_stronglyAdapted (ρ := ρ) D0 hb hs B t t).mono
      ((IndependentBackgroundDriver.filtration (State N) F0).le t)
    apply (Measure.ae_prod_iff_ae_ae
      (hmY.measurableSet_eq_fun (terminal_measurable D0 hb hs t).stronglyMeasurable)).mpr
    filter_upwards [ProductFamily.process_slice_global (ρ := ρ) D0 hb hs B t] with z hz
    filter_upwards [hz, jointProcess_ae D0 hb hs z] with ω hz hj
    exact (hz t le_rfl).trans (hj t).symm
  have hjPull := hφ.quasiMeasurePreserving.ae hYjoint
  filter_upwards [hsame, hjPull] with ω he hj
  exact (he t le_rfl).trans hj

/-- Genuine Chapman–Kolmogorov for the constructed globally Lipschitz,
bounded coefficient SDE. The observed waiting state and future Wiener path
have their proved product law, and the future process is proved by restart. -/
theorem transition_semigroup (B : CoefficientBounds b sigma) (s t : ℝ≥0)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C)
    (x : State N) :
    transition (canonicalDriver N) hb hs (s + t) f x =
      transition (canonicalDriver N) hb hs s
        (transition (canonicalDriver N) hb hs t f) x := by
  let P0 := VectorBrownian.law N
  let D0 := canonicalDriver N
  let X := GlobalSDE.process D0 hb hs x
  have hXa := GlobalSDE.process_stronglyAdapted D0 hb hs x
  have hXm : Measurable (X s) := ((hXa s).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) P0).le s)).measurable
  let ρ := P0.map (X s)
  let : IsProbabilityMeasure ρ := by dsimp [ρ, P0]; infer_instance
  let G : State N × VectorBrownian.Space N → ℝ :=
    fun q => f (jointProcess D0 hb hs q.1 t q.2)
  have hG : StronglyMeasurable G :=
    hf.stronglyMeasurable.comp_measurable (terminal_measurable D0 hb hs t)
  have hGi : Integrable G (ρ.prod P0) :=
    Integrable.of_bound hG.aestronglyMeasurable C (.of_forall (fun _ => hC _))
  let φ : VectorBrownian.Space N → State N × VectorBrownian.Space N :=
    fun ω => (X s ω, BrownianFuturePath.future s ω)
  have hφ : MeasurePreserving φ P0 (ρ.prod P0) :=
    BrownianFutureFiltered.waiting_future_measurePreserving s (X s) (hXa s).measurable
  have hpull : (∫ ω, G (φ ω) ∂P0) = ∫ q, G q ∂ρ.prod P0 := by
    rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable hG.aestronglyMeasurable).symm
  calc
    _ = ∫ ω, f (X (s + t) ω) ∂P0 := transition_eq_actual D0 hb hs _ _ _
    _ = ∫ ω, G (φ ω) ∂P0 := by
      apply integral_congr_ae
      exact (future_restart hb hs B x s t).mono (fun _ h => congrArg f h)
    _ = ∫ q, G q ∂ρ.prod P0 := hpull
    _ = ∫ z, transition D0 hb hs t f z ∂ρ := integral_prod G hGi
    _ = ∫ ω, transition D0 hb hs t f (X s ω) ∂P0 :=
      integral_map hXm.aemeasurable (transition_measurable D0 hb hs t f hf).aestronglyMeasurable
    _ = _ := (transition_eq_actual D0 hb hs s _ x).symm

/-- Literal equality of the actual measurable transition probability
kernels, derived from the expectation semigroup law above. -/
theorem transitionKernel_semigroup (B : CoefficientBounds b sigma)
    (s t : ℝ≥0) (x : State N) :
    transitionKernel (canonicalDriver N) hb hs (s + t) x =
      (transitionKernel (canonicalDriver N) hb hs t ∘ₖ
        transitionKernel (canonicalDriver N) hb hs s) x := by
  let D0 := canonicalDriver N
  let K := transitionKernel D0 hb hs
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hfi : Integrable (fun y => f y) ((K t ∘ₖ K s) x) :=
    Integrable.of_bound f.continuous.stronglyMeasurable.aestronglyMeasurable ‖f‖
      (.of_forall (fun y => f.norm_coe_le_norm y))
  calc
    _ = transition D0 hb hs (s + t) f x :=
      (transition_eq_kernel_integral D0 hb hs (s + t) f f.continuous.stronglyMeasurable x).symm
    _ = transition D0 hb hs s (transition D0 hb hs t f) x :=
      transition_semigroup hb hs B s t f f.continuous ‖f‖ (fun y => f.norm_coe_le_norm y) x
    _ = ∫ z, transition D0 hb hs t f z ∂K s x :=
      transition_eq_kernel_integral D0 hb hs s (transition D0 hb hs t f)
        (transition_measurable D0 hb hs t f f.continuous) x
    _ = ∫ z, ∫ y, f y ∂K t z ∂K s x := by
      apply integral_congr_ae
      exact .of_forall (fun z => transition_eq_kernel_integral D0 hb hs t f
        f.continuous.stronglyMeasurable z)
    _ = _ := (Kernel.integral_comp hfi).symm

end FixedCoefficients

/-- Actual global coefficient bounds for the smooth mixed cutoff.
These are proved from compact support of the cutoff and the literal noise. -/
def mixedCoefficientBounds (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :
    FixedCoefficients.CoefficientBounds
      (cutoffDrift β (mixedGradient μ J) (cutoffRadius N) (cutoffRadius_pos N))
      (CutoffSDE.cutoffNoise N (cutoffRadius N) (cutoffRadius_pos N)) := by
  let hd := cutoffCoefficient_bounded (cutoffRadius N) (cutoffRadius_pos N)
    (drift β (mixedGradient μ J)) (contDiff_drift β _ (mixedGradient_contDiff μ J)).continuous
  let hn := CutoffSDE.cutoffNoise_bounded N (cutoffRadius N) (cutoffRadius_pos N)
  exact ⟨⟨max hd.choose 0, le_max_right _ _⟩, hn.choose,
    (fun i x => ((PiLp.norm_apply_le _ i).trans (hd.choose_spec x)).trans (le_max_left _ _)),
    hn.choose_spec⟩

/-- The actual mixed Langevin transitions form a genuine measurable Markov
kernel; joint measurability was derived from the actual Picard family. -/
def mixedTransitionKernel (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : Kernel (State N) (State N) :=
  FixedCoefficients.transitionKernel (NullAugmentation.driver (VectorBrownian.driver N))
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec t

instance mixedTransitionKernel_markov (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : IsMarkovKernel (mixedTransitionKernel μ J β t) :=
  FixedCoefficients.transitionKernel_markov _ _ _ _

/-- The measurable Markov kernel equals the law of the literal solution. -/
theorem mixedTransitionKernel_apply (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) (x : State N) :
    mixedTransitionKernel μ J β t x = mixedTransitionLaw μ J β t x :=
  FixedCoefficients.transitionKernel_apply _ _ _ _ _

theorem mixedTransitionKernel_zero (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : State N) : mixedTransitionKernel μ J β 0 x = Measure.dirac x := by
  rw [mixedTransitionKernel_apply, mixedTransitionLaw_zero]

theorem mixedTransitionKernel_support (hN : N ≠ 0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    mixedTransitionKernel μ J β t x {y : State N | OnSphere y} = 1 := by
  rw [mixedTransitionKernel_apply]
  exact mixedTransitionLaw_support hN μ J β x hx t

/-- The actual finite mixed Langevin kernels satisfy the literal
Chapman–Kolmogorov identity. No homogeneous-parity restriction is imposed. -/
theorem mixedTransitionKernel_semigroup (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (s t : ℝ≥0) (x : State N) :
    mixedTransitionKernel μ J β (s + t) x =
      (mixedTransitionKernel μ J β t ∘ₖ mixedTransitionKernel μ J β s) x :=
  FixedCoefficients.transitionKernel_semigroup
    (cutoffDrift_lipschitz β _ (mixedGradient_contDiff μ J) _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec
    (mixedCoefficientBounds μ J β) s t x

end SlowEquilibration.SphericalDynamics
