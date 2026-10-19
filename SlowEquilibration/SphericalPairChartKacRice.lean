-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairChartGeometry
public import SlowEquilibration.RoundSphereChartIntegral

/-! Actual full-tensor marked pair Kac--Rice on the genuine product chart. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPairChartKacRice
open MeasureTheory ProbabilityTheory Set Function Metric
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression
open SphericalChartKacRice SphereChartVolume SphericalChartGeometry SphereHessian
open GaussianLocalCoordinates SphericalPairChartGeometry
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal two-point count: simultaneous actual surface-gradient zeros
of the same field, with a Borel mark retaining every original tensor. -/
def actualPairChartCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (s : Set (PairChart n))
    (psi : Disorder (n+1) P → PairChart n → ℝ≥0∞) (J : Disorder (n+1) P) : ℝ≥0∞ :=
  ∑' p : {p : PairChart n | p ∈ s ∧
    surfaceGradient (field c J) (manuscriptChart n p.fst)=0 ∧
    surfaceGradient (field c J) (manuscriptChart n p.snd)=0},psi J p

lemma actualPairChartCount_eq_zeroCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (s : Set (PairChart n)) (hs : s ⊆ pairChartDomain n)
    (psi : Disorder (n+1) P → PairChart n → ℝ≥0∞) (J : Disorder (n+1) P) :
    actualPairChartCount n c s psi J=zeroCount (pairChartGamma n c) s
      (fun g p => psi (unpackDisorder g) p) (euclideanDisorder J) := by
  have he : {p : PairChart n | p ∈ s ∧ pairChartGamma n c p (euclideanDisorder J)=0}=
      {p : PairChart n | p ∈ s ∧
        surfaceGradient (field c J) (manuscriptChart n p.fst)=0 ∧
        surfaceGradient (field c J) (manuscriptChart n p.snd)=0} := by
    ext p
    exact and_congr_right (fun hp => pairChartGamma_intrinsic_zero_iff n c (hs hp) J)
  unfold actualPairChartCount zeroCount
  rw [he]
  simp only [unpack_euclideanDisorder]

/-- Canonical literal-zero pair conditioning is supported on both actual
critical equations, not just an almost-everywhere choice of conditional law. -/
lemma pairKernel_critical_ae {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) (hA : Surjective (pairChartGamma n c p)) :
    ∀ᵐ J ∂coefficientKernel (pairChartGamma n c p) 0,
      surfaceGradient (field c J) (manuscriptChart n p.fst)=0 ∧
      surfaceGradient (field c J) (manuscriptChart n p.snd)=0 := by
  filter_upwards [coefficientKernel_observation_ae (pairChartGamma n c p) hA 0] with J hJ
  exact (pairChartGamma_intrinsic_zero_iff n c hp J).mp hJ

/-- The two genuine chart metric determinants are exactly the factors in
the derivative determinant on the simultaneous critical fiber. -/
lemma pair_conditional_hessian_integral {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) (hA : Surjective (pairChartGamma n c p))
    (psi : Disorder (n+1) P → ℝ≥0∞) :
    (∫⁻ J, ENNReal.ofReal |(spatialJacobian (pairChartGamma n c) (euclideanDisorder J) p).det| * psi J
      ∂coefficientKernel (pairChartGamma n c p) 0)=
      (ENNReal.ofReal (manuscriptChartGram n p.fst).det * ENNReal.ofReal (manuscriptChartGram n p.snd).det) *
        ∫⁻ J, (ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.fst)).det| *
          ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.snd)).det|) * psi J
            ∂coefficientKernel (pairChartGamma n c p) 0 := by
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_congr_ae
  filter_upwards [pairKernel_critical_ae n c hp hA] with J hJ
  rw [pair_spatialJacobian_det n c _ hp]
  change ENNReal.ofReal |(actualChartHessian n c J p.fst).det * (actualChartHessian n c J p.snd).det| * psi J=_
  rw [actualChartHessian_det c J hp.1 hJ.1,actualChartHessian_det c J hp.2 hJ.2]
  simp only [abs_mul,abs_of_pos (manuscriptChartGram_det_pos hp.1),
    abs_of_pos (manuscriptChartGram_det_pos hp.2),
    ENNReal.ofReal_mul (manuscriptChartGram_det_pos hp.1).le,
    ENNReal.ofReal_mul (manuscriptChartGram_det_pos hp.2).le,
    ENNReal.ofReal_mul (mul_nonneg (manuscriptChartGram_det_pos hp.1).le (abs_nonneg _))]
  ac_rfl

/-- Genuine pair marked Kac--Rice on an open product-chart region. Its
surjectivity premise is discharged uniformly below from actual covariance. -/
theorem actual_tensor_pair_chart_kacRice {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (s : Set (PairChart n)) (hs : IsOpen s) (hsub : s ⊆ pairChartDomain n)
    (hA : ∀ p ∈ s,Surjective (pairChartGamma n c p))
    (psi : Disorder (n+1) P → PairChart n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) P × PairChart n => psi p.1 p.2) :
    AEMeasurable (actualPairChartCount n c s psi) (disorderLaw (n+1) P) ∧
    (∫⁻ J,actualPairChartCount n c s psi J ∂disorderLaw (n+1) P)=
      ∫⁻ p in s, GaussianRegression.observationPdf (pairChartGamma n c p) 0 *
        (ENNReal.ofReal (manuscriptChartGram n p.fst).det * ENNReal.ofReal (manuscriptChartGram n p.snd).det) *
        ∫⁻ J, (ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.fst)).det| *
          ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.snd)).det|) * psi J p
            ∂coefficientKernel (pairChartGamma n c p) 0 := by
  let psiE := fun g : EuclideanDisorder (n+1) P => fun p => psi (unpackDisorder g) p
  have hm : Measurable fun p : EuclideanDisorder (n+1) P × PairChart n => psiE p.1 p.2 :=
    hpsi.comp (((unpackCLM (n+1) P).continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have hG := (pairChartGamma_contDiffOn n c).mono hsub
  have hk := marked_kacRice (pairChartGamma n c) s hs hG hA psiE hm
  have hlaw := actual_flattened_gaussian (n+1) P
  have he := funext fun J => actualPairChartCount_eq_zeroCount n c s hsub psi J
  have hMap : AEMeasurable (zeroCount (pairChartGamma n c) s psiE)
      ((disorderLaw (n+1) P).map euclideanDisorder) := by
    rw [hlaw.map_eq]
    exact hk.1
  refine ⟨?_,?_⟩
  · rw [he]
    exact hMap.comp_aemeasurable' hlaw.aemeasurable
  · rw [he,hlaw.lintegral_comp hk.1,hk.2]
    apply setLIntegral_congr_fun hs.measurableSet
    intro p hp
    have hmJ : Measurable (fun J : Disorder (n+1) P =>
        ENNReal.ofReal |(spatialJacobian (pairChartGamma n c) (euclideanDisorder J) p).det| * psi J p) := by
      have h := spatial_mark_measurable (pairChartGamma n c) p
        ((hG.contDiffAt (hs.mem_nhds hp)).differentiableAt_one) psiE hm
      have hg : Measurable (euclideanDisorder (N := n+1) (P := P)) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate (n+1) P => ℝ)).symm.continuous.measurable.comp
          (flatDisorder_measurable _ _)
      simpa only [Function.comp_def,psiE,unpack_euclideanDisorder] using h.comp hg
    have hmap : (∫⁻ g,ENNReal.ofReal |(spatialJacobian (pairChartGamma n c) g p).det| * psiE g p
        ∂GaussianRegression.regressionKernel (pairChartGamma n c p) 0)=
        ∫⁻ J,ENNReal.ofReal |(spatialJacobian (pairChartGamma n c) (euclideanDisorder J) p).det| * psi J p
          ∂coefficientKernel (pairChartGamma n c p) 0 := by
      rw [coefficientKernel_apply,lintegral_map hmJ (unpackCLM (n+1) P).continuous.measurable]
      rfl
    dsimp only
    rw [hmap,pair_conditional_hessian_integral n c (hsub hp) (hA p hp)]
    exact (mul_assoc _ _ _).symm

/-- A proved positive radius on which the actual pair observation is
nondegenerate, selected before the dimension. -/
def pairRadius (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hdeg : 4 ≤ μ.minDegree) : ℝ :=
  min 1 (uniform_pairChartGamma_surjective μ hQ hdeg).choose

lemma pairRadius_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hdeg : 4 ≤ μ.minDegree) :
    0 < pairRadius μ hQ hdeg :=
  lt_min (by norm_num) (uniform_pairChartGamma_surjective μ hQ hdeg).choose_spec.1

def pairOverlapDomain (n : ℕ) (ρ : ℝ) : Set (PairChart n) :=
  pairChartDomain n ∩ {p | |overlap (manuscriptChart n p.fst) (manuscriptChart n p.snd)| < ρ}

lemma pairOverlapDomain_isOpen (n : ℕ) (ρ : ℝ) : IsOpen (pairOverlapDomain n ρ) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
  have h1 := (RoundSphereChartIntegral.manuscriptChart_continuous n).comp e.continuous.fst
  have h2 := (RoundSphereChartIntegral.manuscriptChart_continuous n).comp e.continuous.snd
  exact (pairChartDomain_isOpen n).inter
    (isOpen_lt ((h1.inner h2).div_const _).abs continuous_const)

lemma pairOverlapDomain_surjective (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hdeg : 4 ≤ μ.minDegree) {p : PairChart n}
    (hp : p ∈ pairOverlapDomain n (pairRadius μ hQ hdeg)) :
    Surjective (pairChartGamma n (centerCoefficients (mixtureCoefficients μ) Q) p) :=
  (uniform_pairChartGamma_surjective μ hQ hdeg).choose_spec.2 n p hp.1
    (hp.2.le.trans (min_le_right _ _))

/-- Actual mixed or pure pair Kac--Rice with all nondegeneracy hypotheses
proved from the source degree condition, uniformly in the dimension. -/
theorem actual_pair_chart_smallOverlap_kacRice (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hdeg : 4 ≤ μ.minDegree)
    (psi : Disorder (n+1) μ.maxDegree → PairChart n → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × PairChart n => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := pairOverlapDomain n (pairRadius μ hQ hdeg)
    AEMeasurable (actualPairChartCount n c s psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫⁻ J,actualPairChartCount n c s psi J ∂disorderLaw (n+1) μ.maxDegree)=
      ∫⁻ p in s, GaussianRegression.observationPdf (pairChartGamma n c p) 0 *
        (ENNReal.ofReal (manuscriptChartGram n p.fst).det * ENNReal.ofReal (manuscriptChartGram n p.snd).det) *
        ∫⁻ J, (ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.fst)).det| *
          ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.snd)).det|) * psi J p
            ∂coefficientKernel (pairChartGamma n c p) 0 :=
  actual_tensor_pair_chart_kacRice n _ _ (pairOverlapDomain_isOpen n _) inter_subset_left
    (fun _ hp => pairOverlapDomain_surjective n μ hQ hdeg hp) psi hpsi

end SlowEquilibration.SphericalPairChartKacRice
