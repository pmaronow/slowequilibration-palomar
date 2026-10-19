-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteGaussianField
public import SlowEquilibration.PureTensorJetBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! Uniform convergence of the actual infinite tensor field and its first two
Euclidean jets, from precisely the source square-root coefficient moment. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel PureTensorJetBounds
open scoped Topology RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A measurable envelope of the genuine weighted pure derivative. -/
def blockJetEnvelope {N : ℕ} (μ : InfiniteMixture) (j p : ℕ) (J : Disorder N) : ℝ :=
  Real.sqrt (μ.coeff (p+2))*pureJetEnvelope N (p+2) j (J p)

theorem blockJetEnvelope_nonneg {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (j p : ℕ) (J : Disorder N) : 0≤blockJetEnvelope μ j p J :=
  mul_nonneg (Real.sqrt_nonneg _) (pureJetEnvelope_nonneg hN _)

theorem blockJetEnvelope_continuous {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (j p : ℕ) :
    Continuous (blockJetEnvelope (N := N) μ j p) :=
  continuous_const.mul ((pureJetEnvelope_continuous hN).comp (continuous_apply p))

theorem blockJetEnvelope_integrable {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (j p : ℕ) :
    Integrable (blockJetEnvelope (N := N) μ j p) (disorderLaw N) :=
  ((degree_hasLaw p).integrable_comp (pureJetEnvelope_integrable hN)).const_mul _

theorem blockJetEnvelope_mean_le {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (j p : ℕ) (hj : j≤2) :
    (∫ J,blockJetEnvelope μ j p J ∂disorderLaw N)≤
      8*(N:ℝ)*((p+2:ℕ):ℝ)^(5/2:ℝ)*Real.sqrt (μ.coeff (p+2)) := by
  unfold blockJetEnvelope
  rw [integral_const_mul]
  have he := (degree_hasLaw (N := N) p).integral_comp
    (pureJetEnvelope_integrable (p := p+2) (j := j) hN).aestronglyMeasurable
  dsimp only [Function.comp_def] at he
  rw [he]
  have hb := mul_le_mul_of_nonneg_left
    (expected_pureJetEnvelope_le_five_halves hN (by omega : 2≤p+2) hj)
    (Real.sqrt_nonneg (μ.coeff (p+2)))
  nlinarith

theorem summable_blockJetEnvelope_integral_norm {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (j : ℕ) (hj : j≤2) :
    Summable (fun p => ∫ J,‖blockJetEnvelope μ j p J‖ ∂disorderLaw N) := by
  simp only [Real.norm_of_nonneg (blockJetEnvelope_nonneg hN μ j _ _)]
  apply (μ.summable_shifted_weighted_sqrt (s := 5/2) le_rfl |>.mul_left (8*(N:ℝ))).of_nonneg_of_le
  · intro p
    exact integral_nonneg (blockJetEnvelope_nonneg hN μ j p)
  · intro p
    simpa only [mul_assoc] using blockJetEnvelope_mean_le hN μ j p hj

theorem blockJetEnvelope_summable_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (j : ℕ) (hj : j≤2) :
    ∀ᵐ J ∂disorderLaw N,Summable (fun p => blockJetEnvelope μ j p J) := by
  have he (p : ℕ) : eLpNorm (blockJetEnvelope μ j p) 1 (disorderLaw N)=
      ENNReal.ofReal (∫ J,‖blockJetEnvelope μ j p J‖ ∂disorderLaw N) := by
    rw [eLpNorm_one_eq_lintegral_enorm (blockJetEnvelope_integrable hN μ j p).aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_enorm (blockJetEnvelope_integrable hN μ j p)]
  have hfin : ∑' p,eLpNorm (blockJetEnvelope μ j p) 1 (disorderLaw N)≠⊤ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => integral_nonneg (fun _ => norm_nonneg _))
      (summable_blockJetEnvelope_integral_norm hN μ j hj)]
    exact ENNReal.ofReal_ne_top
  have hh := summable_norm_of_tsum_eLpNorm_ne_top (by rfl : (1:ℝ≥0∞)≤1) hfin
  simpa only [Real.norm_of_nonneg (blockJetEnvelope_nonneg hN μ j _ _)] using hh

/-- One probability-one event controls the actual jets of all three orders. -/
def summableJetDisorder {N : ℕ} (μ : InfiniteMixture) : Set (Disorder N) :=
  {J | ∀ j : ℕ,j≤2 → Summable (fun p => blockJetEnvelope μ j p J)}

theorem summableJetDisorder_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) :
    ∀ᵐ J ∂disorderLaw N,J∈summableJetDisorder μ := by
  simp only [summableJetDisorder,Set.mem_setOf_eq,ae_all_iff]
  exact fun j hj => blockJetEnvelope_summable_ae hN μ j hj

theorem block_contDiff {N : ℕ} (μ : InfiniteMixture) (p : ℕ) (J : Disorder N) :
    ContDiff ℝ ⊤ (block μ p J) :=
  contDiff_const.mul (SphericalAging.FiniteModel.Hamiltonian_contDiff (J p))

theorem block_iteratedFDeriv_norm_le {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (j p : ℕ) (J : Disorder N) (x : Vector N) (hx : ‖x‖≤Real.sqrt N) :
    ‖iteratedFDeriv ℝ j (block μ p J) x‖≤blockJetEnvelope μ j p J := by
  have hf : ContDiffAt ℝ j (SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p)) x :=
    ((SphericalAging.FiniteModel.Hamiltonian_contDiff (J p)).of_le (by simp)).contDiffAt
  change ‖iteratedFDeriv ℝ j (fun x => Real.sqrt (μ.coeff (p+2)) •
    SphericalAging.FiniteModel.Hamiltonian N (p+2) (J p) x) x‖≤_
  rw [iteratedFDeriv_const_smul_apply' hf,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (iteratedFDeriv_norm_le_pureJetEnvelope hN (J p) x hx)
    (Real.sqrt_nonneg _)

theorem jetSeries_tendstoUniformlyOn {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) (j : ℕ) (hj : j≤2) :
    TendstoUniformlyOn (fun s : Finset ℕ => fun x => ∑ p∈s,iteratedFDeriv ℝ j (block μ p J) x)
      (fun x => ∑' p,iteratedFDeriv ℝ j (block μ p J) x) Filter.atTop
      (Metric.closedBall (0 : Vector N) (Real.sqrt N)) := by
  apply tendstoUniformlyOn_tsum (hJ j hj)
  intro p x hx
  exact block_iteratedFDeriv_norm_le hN μ j p J x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem fieldSeries_tendstoUniformlyOn {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) :
    TendstoUniformlyOn (fun s : Finset ℕ => fun x => ∑ p∈s,block μ p J x)
      (field μ J) Filter.atTop (Metric.closedBall (0 : Vector N) (Real.sqrt N)) := by
  apply tendstoUniformlyOn_tsum (hJ 0 (by omega))
  intro p x hx
  simpa only [norm_iteratedFDeriv_zero] using block_iteratedFDeriv_norm_le hN μ 0 p J x
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

end SlowEquilibration.SphericalInfiniteModel
