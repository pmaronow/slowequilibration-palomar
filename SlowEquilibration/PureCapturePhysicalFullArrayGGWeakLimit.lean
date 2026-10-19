-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFullArrayGGTransfer
public import SlowEquilibration.PureCapturePhysicalAsymptoticFullLift

/-! Bounded continuous GG observables on full overlap arrays, allowing
physical finite-volume defects to pass to genuine n→∞ weak limits. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalFullArrayGGWeakLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalFullArrayGGTransfer
open PureCapturePhysicalAsymptoticFullLift
open PureCapturePhysicalAsymptoticScoreLimits
open PureCapturePhysicalAsymptoticGGFromBudget
open PureCapturePhysicalFiniteGGDefinitions
open PureCapturePhysicalPairMeanWeakLimit
open scoped Topology BigOperators BoundedContinuousFunction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

private def bcfOfAbsBound {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (C : ℝ)
    (hb : ∀ x, |f x| ≤ C) : X →ᵇ ℝ := by
  refine ⟨⟨f, hf⟩, ⟨2*C, ?_⟩⟩
  intro x y
  rw [Real.dist_eq]
  calc
    |f x-f y| ≤ |f x|+|f y| := abs_sub _ _
    _ ≤ C+C := add_le_add (hb x) (hb y)
    _ = 2*C := by ring

private theorem covProduct_abs_le {k : ℕ} (μ : FiniteMixture)
    (g : FullOverlapCoordinates k → ℝ) (hgb : ∀ c, |g c| ≤ 1)
    (i j : Fin k) (c : FullOverlapCoordinates k) :
    |g c * clippedArrayCovariance μ i j c| ≤ μ.xi 1 := by
  rw [abs_mul]
  exact (mul_le_mul (hgb c) (clippedArrayCovariance_abs_le μ i j c)
    (abs_nonneg _) (by norm_num)).trans (by simp)

private def covProductBCF {k : ℕ} (μ : FiniteMixture)
    (g : FullOverlapCoordinates k → ℝ) (hg : Continuous g)
    (hgb : ∀ c, |g c| ≤ 1) (i j : Fin k) :
    FullOverlapCoordinates k →ᵇ ℝ :=
  bcfOfAbsBound (fun c => g c * clippedArrayCovariance μ i j c)
    (hg.mul (clippedArrayCovariance_continuous μ i j)) (μ.xi 1)
    (covProduct_abs_le μ g hgb i j)

private def arrayTestBCF {k : ℕ}
    (g : FullOverlapCoordinates k → ℝ) (hg : Continuous g)
    (hgb : ∀ c, |g c| ≤ 1) : FullOverlapCoordinates k →ᵇ ℝ :=
  bcfOfAbsBound g hg 1 hgb

private theorem covProductBCF_apply {k : ℕ} (μ : FiniteMixture)
    (g : FullOverlapCoordinates k → ℝ) (hg : Continuous g)
    (hgb : ∀ c, |g c| ≤ 1) (i j : Fin k)
    (c : FullOverlapCoordinates k) :
    covProductBCF μ g hg hgb i j c =
      g c * clippedArrayCovariance μ i j c := rfl

private theorem arrayTestBCF_apply {k : ℕ}
    (g : FullOverlapCoordinates k → ℝ) (hg : Continuous g)
    (hgb : ∀ c, |g c| ≤ 1) (c : FullOverlapCoordinates k) :
    arrayTestBCF g hg hgb c = g c := rfl

/-- The covariance GG functional is continuous under weak convergence of
full overlap-array laws for bounded continuous tests. -/
theorem fullArrayCovarianceGGDefect_continuous
    (μ : FiniteMixture) (m : ℕ)
    (g : FullOverlapCoordinates (m+1) → ℝ)
    (hg : Continuous g) (hgb : ∀ c, |g c| ≤ 1) :
    Continuous (fun x : FullOverlapLawArray => fullArrayCovarianceGGDefect μ m g x) := by
  let gnew : FullOverlapCoordinates (m+2) → ℝ :=
    fun c => g (fullOverlapPrefix c)
  have hgnew : Continuous gnew := hg.comp fullOverlapPrefix_continuous
  have hgbnew : ∀ c, |gnew c| ≤ 1 := fun c => hgb _
  let Fn := covProductBCF μ gnew hgnew hgbnew 0 (Fin.last (m+1))
  let Fg := arrayTestBCF g hg hgb
  let Fp := covProductBCF μ (fun _ : FullOverlapCoordinates 2 => 1)
    continuous_const (fun _ => by norm_num) 0 1
  let Fo (j : Fin m) := covProductBCF μ g hg hgb 0 j.succ
  have hn : Continuous (fun x : FullOverlapLawArray =>
      ∫ c, Fn c ∂(x (m+2) : Measure (FullOverlapCoordinates (m+2)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction Fn).comp
      (continuous_apply (m+2))
  have hg' : Continuous (fun x : FullOverlapLawArray =>
      ∫ c, Fg c ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction Fg).comp
      (continuous_apply (m+1))
  have hp : Continuous (fun x : FullOverlapLawArray =>
      ∫ c, Fp c ∂(x 2 : Measure (FullOverlapCoordinates 2))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction Fp).comp
      (continuous_apply 2)
  have ho (j : Fin m) : Continuous (fun x : FullOverlapLawArray =>
      ∫ c, Fo j c ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (Fo j)).comp
      (continuous_apply (m+1))
  have hsum : Continuous (fun x : FullOverlapLawArray =>
      ∑ j : Fin m, ∫ c, Fo j c
        ∂(x (m+1) : Measure (FullOverlapCoordinates (m+1)))) :=
    continuous_finsetSum Finset.univ (fun j _ => ho j)
  have hfinal := hn.sub ((hg'.mul hp).div_const ((m : ℝ)+1)) |>.sub
    (hsum.div_const ((m : ℝ)+1))
  convert hfinal using 1
  ext x
  simp only [fullArrayCovarianceGGDefect, Fn, Fg, Fp, Fo, gnew,
    covProductBCF_apply, arrayTestBCF_apply, one_mul,
    Pi.sub_apply, Pi.mul_apply]

/-- Any full-sequence decay of the finite physical full-array GG defects
passes to every genuine n→∞ full-array cluster law. -/
theorem fullArrayCovarianceGGDefect_eq_zero_of_physical_tendsto
    (μ : FiniteMixture) (β : ℝ) (m : ℕ)
    (g : FullOverlapCoordinates (m+1) → ℝ)
    (hg : Continuous g) (hgb : ∀ c, |g c| ≤ 1)
    (hgg : Tendsto (fun n : ℕ =>
      fullArrayCovarianceGGDefect μ m g (physicalFullOverlapLawArray μ β n))
      atTop (𝓝 0))
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    fullArrayCovarianceGGDefect μ m g x = 0 := by
  obtain ⟨s, hs, hfull⟩ :=
    ((mem_tailClusterSet_iff_mapClusterPt _ _).1 hx).tendsto_subseq
  have hlim : Tendsto (fun j : ℕ =>
      fullArrayCovarianceGGDefect μ m g (physicalFullOverlapLawArray μ β (s j)))
      atTop (𝓝 (fullArrayCovarianceGGDefect μ m g x)) :=
    ((fullArrayCovarianceGGDefect_continuous μ m g hg hgb).tendsto x).comp hfull
  exact tendsto_nhds_unique hlim (hgg.comp hs.tendsto_atTop)

/-- If the true unperturbed physical energy deviations are o(N), every
asymptotic full Gibbs overlap-array law obeys covariance GG for bounded
continuous overlap tests. No abstract replica-law identification is assumed. -/
theorem fullArrayCovarianceGGDefect_eq_zero_of_sublinear_budget
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (g : FullOverlapCoordinates (m+1) → ℝ)
    (hg : Continuous g) (hgb : ∀ c, |g c| ≤ 1)
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
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    fullArrayCovarianceGGDefect μ m g x = 0 := by
  let f : (n : ℕ) → (Fin (m+1) → Vector (n+2)) → ℝ :=
    fun _ σ => g (physicalFullOverlapCoordinates σ)
  have hf (n : ℕ) : Measurable (f n) :=
    hg.measurable.comp physicalFullOverlapCoordinates_continuous.measurable
  have hfb (n : ℕ) (σ : Fin (m+1) → Vector (n+2)) : |f n σ| ≤ 1 := hgb _
  have hfinite := physicalCovarianceGGDefect_tendsto_zero_of_sublinear_budget
    μ hβ m f hf hfb hbudget
  have hfull : Tendsto (fun n : ℕ =>
      fullArrayCovarianceGGDefect μ m g (physicalFullOverlapLawArray μ β n))
      atTop (𝓝 0) := by
    simpa only [fullArrayCovarianceGGDefect_physical μ β _ m g hg.measurable] using hfinite
  exact fullArrayCovarianceGGDefect_eq_zero_of_physical_tendsto
    μ β m g hg hgb hfull hx


end SlowEquilibration.PureCapturePhysicalFullArrayGGWeakLimit
