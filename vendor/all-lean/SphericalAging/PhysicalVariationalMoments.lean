module

public import SphericalAging.PhysicalVariationalBounds
public import SphericalAging.VectorSDESecondLocalization
public import SphericalAging.HamiltonianDisorderResponseSolution

public section

/-! True physical Jacobian moments from actual cutoff SDE differentiation.
The entire-vector drift and noise-trace bounds retain the manuscript's
normalization and remove all coordinate-count losses. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalVariationalMoments
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open HamiltonianPicardDependence PhysicalVariationalBounds HamiltonianDisorderResponseSolution
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def physicalDriftBound (p : ℕ) (β : ℝ≥0) (J : FiniteModel.Disorder N p) : ℝ≥0 :=
  1+β*p*(p+1)*⟨GaussianLandscape.landscapeNorm N p J,
    div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)⟩

@[expose] def physicalNoiseTraceBound (N : ℕ) : ℝ≥0 := 8/N

theorem horizonProcess_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x) (T : ℝ≥0)
    {Kb Ks : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) :
    ∀ᵐ ω ∂P,∀ t,t ≤ T → OnSphere
      (GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x T t ω) := by
  let D := NullAugmentation.driver D₀
  let X := GlobalSDE.horizonProcess D hb hs x T
  obtain ⟨Y,hYa,hYc,hYX⟩ := NullAugmentation.exists_allPath_continuous_modification_augmented
    F X (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
      (GlobalSDE.horizonProcess_continuous D hb hs x T)
  have hYsol := AllPathSDE.IsLocalStrongSolutionOn.path_congr
    (GlobalSDE.horizonProcess_strongSolution D hb hs x T) hYa (.of_forall hYc) hYX
  have hYs := (CutoffSphere.physical_solution_of_cutoff hN D β J R hR hNR x hx Y hYc T
    (fun i j => (hs i j).continuous) hYsol).2
  filter_upwards [hYs,hYX] with ω hω he
  intro t ht
  change OnSphere (X t ω)
  rw [← he t]
  exact hω t ht

/-- The actual parameter-response base path preserves the sphere at every
time used by the variational coefficients, without a support premise. -/
theorem baseProcess_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,∀ t,t ≤ T → OnSphere
      (baseProcess (NullAugmentation.driver D₀) β R hR J x T t ω) :=
  horizonProcess_onSphere hN D₀ β J R hR hNR x hx T _ _

/-- Actual native drift and noise derivative matrices satisfy the physical
vector bounds. Their predictability and coarse global cutoff bounds were
constructed in the variational-SDE modules. -/
theorem nativeRows_physical_bounds (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    (∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      ‖WithLp.toLp 2 (fun i => (HamiltonianDisorderLinearization.driftRows
        (NullAugmentation.driver D₀) β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i).value q v)‖ ≤
        physicalDriftBound p β J*‖v‖) ∧
    (∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      (∑ i : Fin N,∑ j : Fin N,((HamiltonianDisorderLinearization.noiseRows
        (NullAugmentation.driver D₀) β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i j).value q v)^2) ≤
        physicalNoiseTraceBound N*‖v‖^2) := by
  let D := NullAugmentation.driver D₀
  let X := baseProcess D β R hR J x T
  have hXs := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (baseProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T)
  constructor
  · filter_upwards [hXs] with q hq
    intro v
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hz : OnSphere (X q.1 q.2) := hq q.1 ht.2
      have hzr : ‖X q.1 q.2‖ < R := by
        have hh := (onSphere_iff_norm_sq _).mp hz
        nlinarith [norm_nonneg (X q.1 q.2),R.coe_nonneg]
      have he : WithLp.toLp 2 (fun i => (HamiltonianDisorderLinearization.driftRows D β R hR
          (‖J‖₊+1) ⟨J,by simp⟩ x T i).value q v)=
          fderiv ℝ (hamiltonianDrift β J) (X q.1 q.2) v := by
        ext i
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)
          (X q.1 q.2) else 0) v = _
        rw [ite_eq_left ht]
        exact fderiv_cutoffDrift_apply β J R hR _ v hzr i
      rw [he]
      change _ ≤ (1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J)*‖v‖
      exact hamiltonianDrift_derivative_norm_le hN hp β.coe_nonneg J (X q.1 q.2) v hz
    · have he : WithLp.toLp 2 (fun i => (HamiltonianDisorderLinearization.driftRows D β R hR
          (‖J‖₊+1) ⟨J,by simp⟩ x T i).value q v)=(0 : State N) := by
        ext i
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)
          (X q.1 q.2) else 0) v = 0
        rw [ite_eq_right ht];rfl
      rw [he,norm_zero]
      positivity
  · filter_upwards [hXs] with q hq
    intro v
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hz : OnSphere (X q.1 q.2) := hq q.1 ht.2
      have hzr : ‖X q.1 q.2‖ < R := by
        have hh := (onSphere_iff_norm_sq _).mp hz
        nlinarith [norm_nonneg (X q.1 q.2),R.coe_nonneg]
      have he (i j : Fin N) : (HamiltonianDisorderLinearization.noiseRows D β R hR
          (‖J‖₊+1) ⟨J,by simp⟩ x T i j).value q v=
          fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) (X q.1 q.2) v := by
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)
          (X q.1 q.2) else 0) v = _
        rw [ite_eq_left ht]
      have heSum : (∑ i : Fin N,∑ j : Fin N,((HamiltonianDisorderLinearization.noiseRows D β R hR
          (‖J‖₊+1) ⟨J,by simp⟩ x T i j).value q v)^2)=
          ∑ i : Fin N,∑ j : Fin N,(fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) (X q.1 q.2) v)^2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => z^2) (he i j)))
      rw [heSum]
      change _ ≤ 8/(N : ℝ)*‖v‖^2
      rw [Finset.sum_comm]
      exact cutoff_noise_square_trace_le hN R hR (X q.1 q.2) v hz hzr
    · have he (i j : Fin N) : (HamiltonianDisorderLinearization.noiseRows D β R hR
          (‖J‖₊+1) ⟨J,by simp⟩ x T i j).value q v=0 := by
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)
          (X q.1 q.2) else 0) v = 0
        rw [ite_eq_right ht];rfl
      have heSum : (∑ i : Fin N,∑ j : Fin N,((HamiltonianDisorderLinearization.noiseRows D β R hR
          (‖J‖₊+1) ⟨J,by simp⟩ x T i j).value q v)^2)=0 := by
        calc
          _ = ∑ i : Fin N,∑ j : Fin N,(0 : ℝ)^2 := Finset.sum_congr rfl
            (fun i _ => Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => z^2) (he i j)))
          _ = 0 := by simp
      rw [heSum]
      positivity

end SphericalAging.PhysicalVariationalMoments
