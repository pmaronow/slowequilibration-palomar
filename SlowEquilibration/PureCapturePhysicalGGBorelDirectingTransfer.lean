-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFullArrayGGBorelExtension
public import SlowEquilibration.PureCapturePhysicalPairMeanDirecting

/-! Transport of bounded-Borel covariance GG from a physical full-overlap
array law to an ordinary IID Hilbert directing representation. The diagonal
is fixed at one on both sides, while physical cube support removes the
covariance clipping on off-diagonal directing overlaps. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalGGBorelDirectingTransfer
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open SlowEquilibration SlowEquilibration.DirectingPhysical
open SphericalModel SphericalForm
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalFullArrayGGTransfer
open SlowEquilibration.PureCapturePhysicalFullArrayGGBorelExtension
open SlowEquilibration.PureCapturePhysicalFullArrayCubeSupport
open SlowEquilibration.PureCapturePhysicalAsymptoticFullLift
open SlowEquilibration.PureCaptureDirectingFullToScore
open SlowEquilibration.PureCapturePhysicalReplicaExclusionDirecting
open SlowEquilibration.PureCapturePhysicalPairMeanDirecting
open SlowEquilibration.PureCapturePhysicalPairMeanWeakLimit
open SlowEquilibration.PureCaptureRandomDirectingScoreArray
open GaussianReplicaKernel GaussianGGEnsemble GaussianGGStarRecursion
open scoped Topology BigOperators
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {Ξ H : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

def fullToPair {m : ℕ} (c : FullOverlapCoordinates m) :
    Fin m × Fin m → ℝ := fun ij => c ij.1 ij.2

theorem fullToPair_measurable {m : ℕ} :
    Measurable (fullToPair (m := m)) := by
  apply Measurable.of_eval
  intro ij
  exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)

theorem fullToPair_directing {m : ℕ} (σ : Fin m → H) :
    fullToPair (directingFullOverlapCoordinates σ) = finiteOverlapArray m σ := by
  funext ij
  rfl

theorem fullOverlapPrefix_directing {m : ℕ} (σ : Fin (m+1) → H) :
    fullOverlapPrefix (directingFullOverlapCoordinates σ) =
      directingFullOverlapCoordinates (initial σ) := by
  ext i j
  simp [fullOverlapPrefix, directingFullOverlapCoordinates, initial]

theorem directingDataFullLaw_integral_comp
    (R : RandomDirectingData Ξ H) (m : ℕ)
    (F : FullOverlapCoordinates m → ℝ) (hF : Measurable F) :
    (∫ c, F c ∂(directingDataFullLaw R m : Measure (FullOverlapCoordinates m))) =
      ∫ σ : Fin m → H, F (directingFullOverlapCoordinates σ)
        ∂law R.disorderLaw R.directingKernel m := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  have hfull : HasLaw (directingFullOverlapCoordinates (H := H) (m := m))
      (directingDataFullLaw R m) (law R.disorderLaw R.directingKernel m) := by
    refine ⟨directingFullOverlapCoordinates_continuous.measurable.aemeasurable, ?_⟩
    rfl
  simpa only [Function.comp_def] using
    (hfull.integral_comp hF.aestronglyMeasurable).symm

theorem directingDataFullLaw_cube_ae
    (R : RandomDirectingData Ξ H) (x : FullOverlapLawArray)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hcube : x ∈ cubeFullOverlapLawArrays) (m : ℕ) :
    ∀ᵐ σ ∂law R.disorderLaw R.directingKernel m,
      directingFullOverlapCoordinates σ ∈ fullOverlapCube m := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  have h := hcube m
  rw [hrep m] at h
  change ∀ᵐ c ∂Measure.map (directingFullOverlapCoordinates (H := H))
    (law R.disorderLaw R.directingKernel m), c ∈ fullOverlapCube m at h
  exact (ae_map_iff directingFullOverlapCoordinates_continuous.measurable.aemeasurable
    (fullOverlapCube_compact m).isClosed.measurableSet).mp h

theorem directing_clippedCovariance_eq_of_cube
    (μ : FiniteMixture) {m : ℕ} (σ : Fin m → H)
    (hσ : directingFullOverlapCoordinates σ ∈ fullOverlapCube m)
    (i j : Fin m) (hij : i ≠ j) :
    clippedArrayCovariance μ i j (directingFullOverlapCoordinates σ) =
      μ.xi (inner ℝ (σ i) (σ j)) := by
  have hc : directingFullOverlapCoordinates σ i j ∈ Icc (-1 : ℝ) 1 :=
    hσ i (by simp) j (by simp)
  have hinner : inner ℝ (σ i) (σ j) ∈ Icc (-1 : ℝ) 1 := by
    simpa [directingFullOverlapCoordinates, hij] using hc
  simp [clippedArrayCovariance, clipOverlap_eq_of_mem_Icc hinner,
    directingFullOverlapCoordinates, hij]

theorem directing_full_covariance_integral
    (μ : FiniteMixture) (R : RandomDirectingData Ξ H)
    (x : FullOverlapLawArray)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hcube : x ∈ cubeFullOverlapLawArrays)
    (m : ℕ) (F : FullOverlapCoordinates m → ℝ)
    (hF : Measurable F) (i j : Fin m) (hij : i ≠ j) :
    (∫ c, F c * clippedArrayCovariance μ i j c
      ∂(x m : Measure (FullOverlapCoordinates m))) =
      ∫ σ : Fin m → H, F (directingFullOverlapCoordinates σ) *
        μ.xi (inner ℝ (σ i) (σ j))
      ∂law R.disorderLaw R.directingKernel m := by
  have hfc : Measurable (fun c : FullOverlapCoordinates m =>
      F c * clippedArrayCovariance μ i j c) :=
    hF.mul (clippedArrayCovariance_continuous μ i j).measurable
  calc
    _ = ∫ c, F c * clippedArrayCovariance μ i j c
      ∂(directingDataFullLaw R m : Measure (FullOverlapCoordinates m)) := by
        rw [hrep m]
    _ = ∫ σ : Fin m → H,
      F (directingFullOverlapCoordinates σ) *
        clippedArrayCovariance μ i j (directingFullOverlapCoordinates σ)
      ∂law R.disorderLaw R.directingKernel m :=
        directingDataFullLaw_integral_comp R m _ hfc
    _ = _ := by
      apply integral_congr_ae
      exact (directingDataFullLaw_cube_ae R x hrep hcube m).mono
        fun σ hσ => by
          change F (directingFullOverlapCoordinates σ) *
            clippedArrayCovariance μ i j (directingFullOverlapCoordinates σ) =
            F (directingFullOverlapCoordinates σ) *
              μ.xi (inner ℝ (σ i) (σ j))
          rw [directing_clippedCovariance_eq_of_cube μ σ hσ i j hij]

theorem directing_full_integral
    (R : RandomDirectingData Ξ H) (x : FullOverlapLawArray)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (m : ℕ) (F : FullOverlapCoordinates m → ℝ) (hF : Measurable F) :
    (∫ c, F c ∂(x m : Measure (FullOverlapCoordinates m))) =
      ∫ σ : Fin m → H, F (directingFullOverlapCoordinates σ)
        ∂law R.disorderLaw R.directingKernel m := by
  rw [hrep m]
  exact directingDataFullLaw_integral_comp R m F hF

theorem finiteOverlapArray_measurable (m : ℕ) :
    Measurable (finiteOverlapArray (H := H) m) := by
  have h := (fullToPair_measurable (m := m)).comp
    (directingFullOverlapCoordinates_continuous (H := H) (m := m)).measurable
  convert h using 1
  funext σ
  exact (fullToPair_directing σ).symm

theorem covarianceGG_of_fullArrayGG
    (μ : FiniteMixture) (R : RandomDirectingData Ξ H)
    (x : FullOverlapLawArray)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hcube : x ∈ cubeFullOverlapLawArrays)
    (hball : ∀ᵐ ω ∂(R.disorderLaw),
      ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1)
    (harray : ∀ m f, Measurable f → (∀ c, |f c| ≤ 1) →
      fullArrayCovarianceGGDefect μ m f x = 0) :
    CovarianceGG R.disorderLaw R.directingKernel μ.xi := by
  letI : IsProbabilityMeasure R.disorderLaw := R.disorderProbability
  letI : IsMarkovKernel R.directingKernel := R.directingMarkov
  intro m f hf hfb
  let g : FullOverlapCoordinates (m+1) → ℝ := fun c => f (fullToPair c)
  have hg : Measurable g := hf.comp fullToPair_measurable
  have hgb (c : FullOverlapCoordinates (m+1)) : |g c| ≤ 1 := hfb _
  have hGG := harray m g hg hgb
  have hpair :
      (∫ c, clippedArrayCovariance μ 0 1 c
        ∂(x 2 : Measure (FullOverlapCoordinates 2))) =
      ∫ r, μ.xi r ∂overlapLaw R.disorderLaw R.directingKernel := by
    have hmean := directingPairCovarianceMean_eq_fullArrayMean
      μ R x hrep hcube hball
    calc
      _ = ∫ c, μ.xi (c 0 1)
          ∂(x 2 : Measure (FullOverlapCoordinates 2)) := by
            apply integral_congr_ae
            exact (hcube 2).mono fun c hc => by
              change clippedArrayCovariance μ 0 1 c = μ.xi (c 0 1)
              exact clippedPairCovariance_eq_on_cube μ hc
      _ = _ := hmean.symm
  have hnew :
      (∫ c : FullOverlapCoordinates (m+2),
        g (fullOverlapPrefix c) *
          clippedArrayCovariance μ 0 (Fin.last (m+1)) c
        ∂(x (m+2) : Measure (FullOverlapCoordinates (m+2)))) =
      ∫ σ : Fin (m+2) → H,
        f (finiteOverlapArray (m+1) (initial σ)) *
          μ.xi (freshOverlap m σ)
        ∂law R.disorderLaw R.directingKernel (m+2) := by
    rw [directing_full_covariance_integral μ R x hrep hcube (m+2)
      (fun c => g (fullOverlapPrefix c))
      (hg.comp fullOverlapPrefix_continuous.measurable)
      0 (Fin.last (m+1)) (by simp [Fin.last])]
    apply integral_congr_ae
    exact .of_forall fun σ => by
      change g (fullOverlapPrefix (directingFullOverlapCoordinates σ)) *
        μ.xi (inner ℝ (σ 0) (σ (Fin.last (m+1)))) =
          f (finiteOverlapArray (m+1) (initial σ)) * μ.xi (freshOverlap m σ)
      rw [fullOverlapPrefix_directing]
      change f (fullToPair (directingFullOverlapCoordinates (initial σ))) *
        μ.xi (inner ℝ (σ 0) (σ (Fin.last (m+1)))) =
        f (finiteOverlapArray (m+1) (initial σ)) * μ.xi (freshOverlap m σ)
      rw [fullToPair_directing]
      rfl
  have hbase :
      (∫ c : FullOverlapCoordinates (m+1), g c
        ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) =
      ∫ σ : Fin (m+1) → H,
        f (finiteOverlapArray (m+1) σ)
        ∂law R.disorderLaw R.directingKernel (m+1) := by
    rw [directing_full_integral R x hrep (m+1) g hg]
    apply integral_congr_ae
    exact .of_forall fun σ => by
      change f (fullToPair (directingFullOverlapCoordinates σ)) =
        f (finiteOverlapArray (m+1) σ)
      rw [fullToPair_directing]
  have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr fun r =>
    (μ.hasDerivAt_xi r).continuousAt
  have hold (j : Fin m) :
      (∫ c : FullOverlapCoordinates (m+1),
        g c * clippedArrayCovariance μ 0 j.succ c
        ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) =
      ∫ σ : Fin (m+2) → H,
        f (finiteOverlapArray (m+1) (initial σ)) *
          μ.xi (oldOverlap m j σ)
        ∂law R.disorderLaw R.directingKernel (m+2) := by
    rw [directing_full_covariance_integral μ R x hrep hcube (m+1)
      g hg 0 j.succ (Fin.succ_ne_zero j).symm]
    let F : (Fin (m+1) → H) → ℝ := fun σ =>
      f (finiteOverlapArray (m+1) σ) * μ.xi (inner ℝ (σ 0) (σ j.succ))
    have hF : Measurable F := by
      apply (hf.comp (finiteOverlapArray_measurable (H := H) (m+1))).mul
      exact (hxi.comp ((continuous_apply (0 : Fin (m+1))).inner
        (continuous_apply j.succ))).measurable
    have hp := (initial_hasLaw R.disorderLaw R.directingKernel (m+1)).integral_comp
      hF.aestronglyMeasurable
    calc
      _ = ∫ σ : Fin (m+1) → H, F σ
          ∂law R.disorderLaw R.directingKernel (m+1) := by
            apply integral_congr_ae
            exact .of_forall fun σ => by
              change f (fullToPair (directingFullOverlapCoordinates σ)) *
                μ.xi (inner ℝ (σ 0) (σ j.succ)) = F σ
              rw [fullToPair_directing]
      _ = ∫ σ : Fin (m+2) → H, F (initial σ)
          ∂law R.disorderLaw R.directingKernel (m+2) := by
            simpa only [Function.comp_def] using hp.symm
      _ = _ := by
        apply integral_congr_ae
        exact .of_forall fun σ => by
          rfl
  unfold fullArrayCovarianceGGDefect at hGG
  rw [hnew, hbase, hpair] at hGG
  simp_rw [hold] at hGG
  linear_combination hGG

/-- The original physical Hamiltonian's sublinear energy deviation gives
covariance GG to every directing representation of a physical weak limit. -/
theorem covarianceGG_of_physical_sublinear_budget
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (hbudget : Tendsto (fun n : ℕ =>
      (GaussianPerturbationDeviation.meanThermalDeviation
          (PureCapturePhysicalShellGG.shellLaw (n+2))
          (PureCapturePhysicalShellGG.shellLinear (mixtureCoefficients μ))
          (fun _ => true) β +
        GaussianPerturbationIntegrated.energyFluctuation
          (PureCapturePhysicalShellGG.shellLaw (n+2))
          (PureCapturePhysicalShellGG.shellLinear (mixtureCoefficients μ))
          (fun _ => true) β) / ((n+2 : ℕ) : ℝ)) atTop (𝓝 0))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β)
    (R : RandomDirectingData Ξ H)
    (hrep : ∀ m, x m = directingDataFullLaw R m)
    (hball : ∀ᵐ ω ∂(R.disorderLaw),
      ∀ᵐ v ∂(R.directingKernel ω), ‖v‖ ≤ 1) :
    CovarianceGG R.disorderLaw R.directingKernel μ.xi := by
  apply covarianceGG_of_fullArrayGG μ R x hrep
    (physicalFullAsymptoticLimitSet_cube μ β hx) hball
  intro m f hf hfb
  exact fullArrayCovarianceGGDefect_eq_zero_borel_of_sublinear_budget
    μ hβ m f hf hfb hbudget hx

end SlowEquilibration.PureCapturePhysicalGGBorelDirectingTransfer
