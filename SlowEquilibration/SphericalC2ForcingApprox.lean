module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalPoissonEquation
public import SlowEquilibration.UniformSmoothC2Approximation
public import SlowEquilibration.C1SphericalGraph
public import SlowEquilibration.SphericalFormCore

@[expose] public section

/-! # True smooth approximation in the actual spherical generator graph -/

namespace SlowEquilibration.SphericalPoissonPrimitive
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalForm
open SphericalAging.HardSphereDynamics
open scoped InnerProductSpace Topology ContDiff BigOperators
variable {N : ℕ}

local instance firstJetNormed (N : ℕ) : NormedAddCommGroup (Vector N →L[ℝ] ℝ) := inferInstance
local instance firstJetSpace (N : ℕ) : NormedSpace ℝ (Vector N →L[ℝ] ℝ) := inferInstance
local instance secondJetNormed (N : ℕ) : NormedAddCommGroup (Vector N →L[ℝ] Vector N →L[ℝ] ℝ) := inferInstance
local instance secondJetSpace (N : ℕ) : NormedSpace ℝ (Vector N →L[ℝ] Vector N →L[ℝ] ℝ) := inferInstance

/-- The actual drift/noise coefficient controlling a C² generator difference. -/
def physicalCoefficientSize (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (x : Vector N) : ℝ :=
  ‖drift β (mixedGradient μ J) x‖ + (1/2:ℝ)*∑ j : Fin N, ‖noiseColumn x j‖^2

lemma physicalCoefficientSize_nonneg (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : Vector N) :
    0 ≤ physicalCoefficientSize μ J β x := by unfold physicalCoefficientSize; positivity

lemma physicalCoefficientSize_continuous (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) : Continuous (physicalCoefficientSize μ J β) := by
  have hb := (contDiff_drift β _ (mixedGradient_contDiff μ J)).continuous
  have hn (j : Fin N) := (contDiff_noiseColumn j).continuous
  exact hb.norm.add ((continuous_finsetSum _ (fun j _ => (hn j).norm.pow 2)).const_mul _)

lemma exists_physicalCoefficientSize_bound (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vector N, OnSphere x → physicalCoefficientSize μ J β x ≤ C := by
  obtain ⟨C, hC⟩ := (physicalSphere_compact N).exists_bound_of_continuousOn
    (physicalCoefficientSize_continuous μ J β).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h := (hC x hx).trans (le_max_left C 0)
  simpa only [Real.norm_of_nonneg (physicalCoefficientSize_nonneg μ J β x)] using h

lemma mixedGenerator_dist_le (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f g : Vector N → ℝ) (x : Vector N) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : dist (fderiv ℝ f x) (fderiv ℝ g x) ≤ δ)
    (hdd : dist (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ g) x) ≤ δ) :
    dist (mixedGenerator μ J β f x) (mixedGenerator μ J β g x) ≤
      physicalCoefficientSize μ J β x * δ := by
  let b := drift β (mixedGradient μ J) x
  let σ := noiseColumn x
  have h₁ : ‖(fderiv ℝ f x - fderiv ℝ g x) b‖ ≤ δ*‖b‖ :=
    ((fderiv ℝ f x - fderiv ℝ g x).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using hd) (norm_nonneg b))
  have h₂ (j : Fin N) :
      ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x) (σ j) (σ j)‖ ≤ δ*‖σ j‖^2 := by
    calc
      _ ≤ ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x) (σ j)‖*‖σ j‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x‖*‖σ j‖)*‖σ j‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (δ*‖σ j‖)*‖σ j‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using hdd) (norm_nonneg _))
        (norm_nonneg _)
      _ = _ := by ring
  have he : mixedGenerator μ J β f x - mixedGenerator μ J β g x =
      (fderiv ℝ f x-fderiv ℝ g x) b + (1/2:ℝ)*∑ j : Fin N,
        (fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) x) (σ j) (σ j) := by
    simp only [mixedGenerator_as_jet, mixedJet, coefficientJet_apply,
      sub_apply, Finset.sum_sub_distrib, b, σ]
    ring
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖(fderiv ℝ f x-fderiv ℝ g x) b‖ +
        ‖(1/2:ℝ)*∑ j : Fin N, (fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) x) (σ j) (σ j)‖ := norm_add_le _ _
    _ ≤ δ*‖b‖ + (1/2:ℝ)*∑ j : Fin N, δ*‖σ j‖^2 := by
      apply add_le_add h₁
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => h₂ j))
    _ = _ := by rw [← Finset.mul_sum]; dsimp [physicalCoefficientSize, b, σ]; ring

/-- Literal value minus actual physical generator for an ambient C² function. -/
def C2Forcing (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) : Lp ℝ 2 (mixtureGibbsLaw μ β J) :=
  gibbsToL2 hN β (fieldOfMixture μ J) (fieldOfMixture_contDiff μ J).continuous
    (fun x => f x - mixedGenerator μ J β f x)
    (hf.continuous.sub (Ito.generator_continuous β _ (mixedGradient_contDiff μ J) hf))

/-- Genuine C∞ approximants converge in both actual value and actual
second-order differential generator in Gibbs L². -/
theorem exists_smoothForcing_tendsto (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ g : ℕ → smoothCore N,
      Tendsto (fun n => smoothResolventForcing hN β (fieldOfMixture μ J)
        ((fieldOfMixture_contDiff μ J).of_le (by simp)) (g n)) atTop
        (𝓝 (C2Forcing hN μ J β f hf)) := by
  obtain ⟨g, hg, hv, hd, hdd⟩ :=
    UniformSmoothC2Approximation.exists_uniform_smooth_C2_sequence_compact
      (volume : Measure (Vector N)) f hf hfc
  obtain ⟨C, hC, hbound⟩ := exists_physicalCoefficientSize_bound μ J β
  let gs : ℕ → smoothCore N := fun n => ⟨g n, (hg n).1⟩
  refine ⟨gs, ?_⟩
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (1+C)
  simp only [zero_mul] at ht
  have happrox := gibbsToL2_tendsto_of_ae_bound hN β (fieldOfMixture μ J)
    (fieldOfMixture_contDiff μ J).continuous
    (fun n x => g n x - mixedGenerator μ J β (g n) x)
    (fun x => f x - mixedGenerator μ J β f x)
    (fun n => (hg n).1.continuous.sub
      (Ito.generator_continuous β _ (mixedGradient_contDiff μ J) ((hg n).1.of_le (by simp))))
    (hf.continuous.sub (Ito.generator_continuous β _ (mixedGradient_contDiff μ J) hf))
    (fun n => (1/((n:ℝ)+1))*(1+C)) (fun n => by positivity) ht (fun n => ?_)
  · change Tendsto _ atTop (𝓝 (gibbsToL2 hN β (fieldOfMixture μ J)
        (fieldOfMixture_contDiff μ J).continuous
        (fun x => f x - mixedGenerator μ J β f x) _))
    apply happrox.congr'
    apply Eventually.of_forall
    intro n
    symm
    apply gibbsToL2_congr
    filter_upwards [gibbsLaw_support hN β (fieldOfMixture μ J)] with x hx
    have hxs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
    simp only [gs, smoothResolventForcing]
    rw [mixedGenerator_eq_rotationGenerator (by omega) μ J β ((hg n).1.of_le (by simp)) x hxs]
  · filter_upwards [gibbsLaw_support hN β (fieldOfMixture μ J)] with x hx
    have hxs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
    have hb := mixedGenerator_dist_le μ J β (g n) f x (by positivity) (hd n x) (hdd n x)
    have hb' := hb.trans (mul_le_mul_of_nonneg_right (hbound x hxs) (by positivity))
    calc
      _ ≤ dist (g n x) (f x) +
        dist (mixedGenerator μ J β (g n) x) (mixedGenerator μ J β f x) := dist_sub_sub_le _ _ _ _
      _ ≤ 1/((n:ℝ)+1) + C*(1/((n:ℝ)+1)) := add_le_add (hv n x) hb'
      _ = _ := by ring

end
end SlowEquilibration.SphericalPoissonPrimitive
