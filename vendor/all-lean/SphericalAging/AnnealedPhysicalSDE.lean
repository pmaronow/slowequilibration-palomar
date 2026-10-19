module

public import SphericalAging.AnnealedCutoffSDE
public import SphericalAging.AnnealedSphereProcess

public section

/-! Actual untruncated annealed finite-N hard-sphere Hamiltonian SDE.
Sphere preservation is proved from the actual cutoff product SDE, and then
the cutoff is removed from the genuine predictable classes and real drift
integrals. Disorder and initial data remain random background coordinates.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AnnealedPhysicalSDE
open HardSphereDynamics AnnealedCutoffProcess AnnealedCutoffCoefficients AnnealedSDECore
open IndependentBackgroundDriver
set_option maxHeartbeats 1000000
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}
  {ρ : Measure (Parameter N p)} [IsProbabilityMeasure ρ]

/-- Actual random-disorder physical dynamics on every finite horizon,
with a proved common-event sphere bound. All coefficient-class and actual
matrix Itô identities are theorem conclusions. -/
theorem process_strongSolution (hN : N ≠ 0) (D : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (hJ : MemLp (fun q : Parameter N p => q.1) 2 ρ)
    (hinitial : ∀ᵐ q ∂ρ, OnSphere q.2) (T : ℝ≥0) :
    IsRandomStrongSolutionOn (driver (ρ := ρ) (NullAugmentation.driver D))
      (fun ω i x => hamiltonianDrift β ω.1.1 x i)
      (fun _ i j x => noiseColumn x j i) (fun ω => ω.1.2)
      (process (NullAugmentation.driver D) β R hR hJ T) T ∧
    (∀ᵐ ω ∂ρ.prod P, ∀ t, t ≤ T → OnSphere (process (NullAugmentation.driver D) β R hR hJ T t ω)) := by
  let D' := NullAugmentation.driver D
  let X := process D' β R hR hJ T
  have hsphere := AnnealedSphereProcess.process_onSphere hN D β R hR hNR hJ hinitial T
  have hbound : ∀ᵐ ω ∂ρ.prod P, ∀ t, t ≤ T → ‖X t ω‖ ≤ R := by
    filter_upwards [hsphere] with ω hs
    intro t ht
    have hsq := (onSphere_iff_norm_sq (X t ω)).mp (hs t ht)
    nlinarith [norm_nonneg (X t ω),R.coe_nonneg]
  rcases AnnealedCutoffSDE.process_strongSolution D' β R hR hJ T with ⟨hi,ha,hc,A,U,hA,hU,heq⟩
  refine ⟨⟨hi,ha,hc,A,U,?_,?_,?_⟩,hsphere⟩
  · intro i
    have hb := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := ρ.prod P)).ae hbound
    filter_upwards [hA i,hb] with z hAz hz
    rw [hAz]
    by_cases ht : z.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht]
      exact CutoffSDE.cutoffDrift_eq β z.2.1.1 R hR _ (hz z.1 ht.2) i
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right ht]
  · intro i j
    have hb := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := ρ.prod P)).ae hbound
    filter_upwards [hU i j,hb] with z hUz hz
    rw [hUz]
    by_cases ht : z.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht]
      exact CutoffSDE.cutoffNoise_eq N R hR _ (hz z.1 ht.2) i j
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right ht]
  · intro t ht i
    filter_upwards [heq t ht i,hbound] with ω heq hb
    have hd : (∫ s in (0 : ℝ)..(t : ℝ), CutoffSDE.cutoffDrift β ω.1.1 R hR i (X s.toNNReal ω)) =
        ∫ s in (0 : ℝ)..(t : ℝ), hamiltonianDrift β ω.1.1 (X s.toNNReal ω) i := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hst : s ≤ (t : ℝ) := (show s ∈ Icc (0 : ℝ) (t : ℝ) from by
        simpa only [uIcc_of_le t.coe_nonneg] using hs).2
      have hsNN : s.toNNReal ≤ t := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_mono hst
      exact CutoffSDE.cutoffDrift_eq β ω.1.1 R hR _ (hb s.toNNReal (hsNN.trans ht)) i
    exact heq.trans (congrArg (fun d => ω.1.2 i+d+
      (VectorIto.vectorProcessLp (driver (ρ := ρ) D') (U i) t : Parameter N p × Ω → ℝ) ω) hd)

end SphericalAging.AnnealedPhysicalSDE
