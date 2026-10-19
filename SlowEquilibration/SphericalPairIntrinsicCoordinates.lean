-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairChartGeometry

/-! Coordinate-free complete tangent pair observations and exact metric
factors for their actual chart density and full-coefficient zero kernel. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPairIntrinsicCoordinates
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression
open SphericalChartKacRice SphereChartVolume SphericalChartGeometry SphereHessian
open IntrinsicGradientRegression SphericalPairChartGeometry GaussianObservationCoercivity
open GaussianRegression
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section HilbertProduct
variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']

def hilbertProductEquiv (e : E ≃L[ℝ] E') (f : F ≃L[ℝ] F') :
    WithLp 2 (E×F) ≃L[ℝ] WithLp 2 (E'×F') :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).trans
    ((e.prodCongr f).trans (WithLp.prodContinuousLinearEquiv 2 ℝ E' F').symm)

lemma hilbertProductEquiv_apply (e : E ≃L[ℝ] E') (f : F ≃L[ℝ] F') (p : WithLp 2 (E×F)) :
    hilbertProductEquiv e f p=WithLp.toLp 2 (e p.fst,f p.snd) := rfl

lemma hilbertProductEquiv_adjoint_apply (e : E ≃L[ℝ] E') (f : F ≃L[ℝ] F')
    (p : WithLp 2 (E'×F')) :
    (hilbertProductEquiv e f : WithLp 2 (E×F) →L[ℝ] WithLp 2 (E'×F')).adjoint p=
      WithLp.toLp 2 ((e : E →L[ℝ] E').adjoint p.fst,(f : F →L[ℝ] F').adjoint p.snd) := by
  apply ext_inner_left ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearEquiv.coe_coe,hilbertProductEquiv_apply,WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  change inner ℝ (e q.fst) p.fst+inner ℝ (f q.snd) p.snd =
    inner ℝ q.fst ((e : E →L[ℝ] E').adjoint p.fst)+inner ℝ q.snd ((f : F →L[ℝ] F').adjoint p.snd)
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  rfl

def hilbertProductMap (A : E →L[ℝ] E) (B : F →L[ℝ] F) : WithLp 2 (E×F) →L[ℝ] WithLp 2 (E×F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    ((A.prodMap B).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap)

lemma hilbertProductMap_det (A : E →L[ℝ] E) (B : F →L[ℝ] F) :
    (hilbertProductMap A B).det=A.det*B.det := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  change LinearMap.det (e.symm.toLinearEquiv.toLinearMap ∘ₗ (A.toLinearMap.prodMap B.toLinearMap) ∘ₗ
    e.toLinearEquiv.toLinearMap)=_
  exact (LinearMap.det_conj _ e.toLinearEquiv.symm).trans (LinearMap.det_prodMap _ _)

lemma hilbertProductEquiv_gram_det (e : E ≃L[ℝ] E') (f : F ≃L[ℝ] F') :
    ((hilbertProductEquiv e f).toContinuousLinearMap.adjoint.comp (hilbertProductEquiv e f).toContinuousLinearMap).det=
      ((e : E →L[ℝ] E').adjoint.comp (e : E →L[ℝ] E')).det *
        ((f : F →L[ℝ] F').adjoint.comp (f : F →L[ℝ] F')).det := by
  have he : (hilbertProductEquiv e f).toContinuousLinearMap.adjoint.comp (hilbertProductEquiv e f).toContinuousLinearMap=
      hilbertProductMap ((e : E →L[ℝ] E').adjoint.comp (e : E →L[ℝ] E'))
        ((f : F →L[ℝ] F').adjoint.comp (f : F →L[ℝ] F')) := by
    ext p
    rw [ContinuousLinearMap.comp_apply,hilbertProductEquiv_adjoint_apply,ContinuousLinearEquiv.coe_coe,hilbertProductEquiv_apply]
    rfl
  rw [he,hilbertProductMap_det]
end HilbertProduct

/-- Both actual complete intrinsic gradients of the same coefficient field. -/
def pairIntrinsicGamma {N P : ℕ} (c : Degree P → ℝ) (x y : Vector N) :
    EuclideanDisorder N P →L[ℝ] WithLp 2 (tangentPlane x × tangentPlane y) :=
  pairHilbert (intrinsicGamma c x) (intrinsicGamma c y)

def pairTangentEquiv {n : ℕ} (p : PairChart n) (hp : p ∈ pairChartDomain n) :
    PairChart n ≃L[ℝ] WithLp 2 (tangentPlane (manuscriptChart n p.fst) × tangentPlane (manuscriptChart n p.snd)) :=
  hilbertProductEquiv (chartTangentEquiv p.fst hp.1) (chartTangentEquiv p.snd hp.2)

lemma pairChartGamma_eq_adjoint_intrinsic {n P : ℕ} (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) :
    pairChartGamma n c p=(pairTangentEquiv p hp).toContinuousLinearMap.adjoint.comp
      (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd)) := by
  ext g
  rw [ContinuousLinearMap.comp_apply,pairTangentEquiv,hilbertProductEquiv_adjoint_apply]
  change WithLp.toLp 2 (chartGamma n c p.fst g,chartGamma n c p.snd g)=_
  rw [chartGamma_eq_adjoint_intrinsic c hp.1,chartGamma_eq_adjoint_intrinsic c hp.2]
  rfl

lemma pairTangentEquiv_gram_det {n : ℕ} {p : PairChart n} (hp : p ∈ pairChartDomain n) :
    ((pairTangentEquiv p hp).toContinuousLinearMap.adjoint.comp (pairTangentEquiv p hp).toContinuousLinearMap).det=
      (manuscriptChartGram n p.fst).det*(manuscriptChartGram n p.snd).det := by
  rw [pairTangentEquiv,hilbertProductEquiv_gram_det,
    chartTangentEquiv_gram_det hp.1,chartTangentEquiv_gram_det hp.2]

lemma pairChartGamma_gram_det {n P : ℕ} (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) :
    (gram (pairChartGamma n c p)).det=
      ((manuscriptChartGram n p.fst).det*(manuscriptChartGram n p.snd).det)*
        (gram (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd))).det := by
  rw [pairChartGamma_eq_adjoint_intrinsic c hp]
  have he : gram ((pairTangentEquiv p hp).toContinuousLinearMap.adjoint.comp
      (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd)))=
      pullback (pairTangentEquiv p hp)
        (gram (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd))) := by
    simp only [gram,pullback,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc]
  rw [he,pullback_det,pairTangentEquiv_gram_det hp]

lemma pairIntrinsicGamma_surjective_of_chart {n P : ℕ} (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) (hA : Surjective (pairChartGamma n c p)) :
    Surjective (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd)) := by
  intro w
  obtain ⟨g,hg⟩ := hA ((pairTangentEquiv p hp).toContinuousLinearMap.adjoint w)
  refine ⟨g,adjoint_equiv_injective (pairTangentEquiv p hp) ?_⟩
  rw [pairChartGamma_eq_adjoint_intrinsic c hp] at hg
  exact hg

/-- Equality at the specified null conditioning target, for the full
original coefficient laws, from equality of the actual zero fibers. -/
lemma pair_chart_coefficientKernel_zero_eq {n P : ℕ} (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) (hA : Surjective (pairChartGamma n c p)) :
    coefficientKernel (pairChartGamma n c p) 0=
      coefficientKernel (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd)) 0 := by
  apply coefficientKernel_zero_eq_of_ker_eq _ _ hA (pairIntrinsicGamma_surjective_of_chart c hp hA)
  ext g
  change pairChartGamma n c p g=0 ↔ pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd) g=0
  rw [pairChartGamma_eq_adjoint_intrinsic c hp]
  change (pairTangentEquiv p hp).toContinuousLinearMap.adjoint
    (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd) g)=0 ↔ _
  rw [← map_zero (pairTangentEquiv p hp).toContinuousLinearMap.adjoint]
  exact (adjoint_equiv_injective (pairTangentEquiv p hp)).eq_iff

/-- Coordinate density times both Hessian metric determinants leaves the
intrinsic pair density and the two genuine round-area densities. -/
theorem pair_density_metric_cancel {n P : ℕ} (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) (hA : Surjective (pairChartGamma n c p)) :
    observationPdf (pairChartGamma n c p) 0 *
      (ENNReal.ofReal (manuscriptChartGram n p.fst).det * ENNReal.ofReal (manuscriptChartGram n p.snd).det)=
    observationPdf (pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd)) 0 *
      (ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.fst).det) *
        ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.snd).det)) := by
  let A := pairIntrinsicGamma c (manuscriptChart n p.fst) (manuscriptChart n p.snd)
  have hn : GaussianDensity.normalizer (PairChart n)=
      GaussianDensity.normalizer (WithLp 2 (tangentPlane (manuscriptChart n p.fst) × tangentPlane (manuscriptChart n p.snd))) := by
    unfold GaussianDensity.normalizer
    rw [(pairTangentEquiv p hp).toLinearEquiv.finrank_eq]
  have hd1 := manuscriptChartGram_det_pos hp.1
  have hd2 := manuscriptChartGram_det_pos hp.2
  have hd := gram_det_pos A (pairIntrinsicGamma_surjective_of_chart c hp hA)
  rw [observationPdf_zero,observationPdf_zero,pairChartGamma_gram_det c hp,hn]
  rw [← ENNReal.ofReal_mul hd1.le,← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul (div_nonneg GaussianDensity.normalizer_pos.le (Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul (div_nonneg GaussianDensity.normalizer_pos.le (Real.sqrt_nonneg _))]
  congr 1
  rw [← Real.sqrt_mul hd1.le,Real.sqrt_mul (mul_pos hd1 hd2).le]
  have hsd := (Real.sqrt_pos.mpr hd).ne'
  have hsm := (Real.sqrt_pos.mpr (mul_pos hd1 hd2)).ne'
  rw [← Real.sq_sqrt (mul_pos hd1 hd2).le]
  field_simp
  simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]

end SlowEquilibration.SphericalPairIntrinsicCoordinates
