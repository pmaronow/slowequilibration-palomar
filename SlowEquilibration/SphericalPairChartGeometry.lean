-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalIntrinsicChartKacRice
public import SlowEquilibration.SphericalSequentialRegression
public import SlowEquilibration.PairObservationSmallOverlap
public import SlowEquilibration.ValueObservationSmallOverlap

/-! The actual two-point coordinate gradient and its genuine block Hessian.
Both points observe the same original Gaussian tensor disorder. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPairChartGeometry
open MeasureTheory ProbabilityTheory Set Function Metric
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression
open SphericalChartKacRice SphereChartVolume SphericalChartGeometry SphereHessian
open IntrinsicGradientRegression IntrinsicHessianLaw SphericalSequentialRegression
open GaussianLocalCoordinates GaussianObservationCoercivity
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ProductDerivative
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma hilbert_product_derivative (f : U → U) (g : V → V) (p : WithLp 2 (U×V))
    (hf : DifferentiableAt ℝ f p.fst) (hg : DifferentiableAt ℝ g p.snd) :
    fderiv ℝ (fun q : WithLp 2 (U×V) => WithLp.toLp 2 (f q.fst,g q.snd)) p =
      (WithLp.prodContinuousLinearEquiv 2 ℝ U V).symm.toContinuousLinearMap.comp
        (((fderiv ℝ f p.fst).prodMap (fderiv ℝ g p.snd)).comp
          (WithLp.prodContinuousLinearEquiv 2 ℝ U V).toContinuousLinearMap) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ U V
  have h := e.symm.hasFDerivAt.comp p
    ((HasFDerivAt.prodMap (e p) hf.hasFDerivAt hg.hasFDerivAt).comp p e.hasFDerivAt)
  exact h.fderiv
variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
lemma hilbert_product_derivative_det (f : U → U) (g : V → V) (p : WithLp 2 (U×V))
    (hf : DifferentiableAt ℝ f p.fst) (hg : DifferentiableAt ℝ g p.snd) :
    (fderiv ℝ (fun q : WithLp 2 (U×V) => WithLp.toLp 2 (f q.fst,g q.snd)) p).det =
      (fderiv ℝ f p.fst).det*(fderiv ℝ g p.snd).det := by
  rw [hilbert_product_derivative f g p hf hg]
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ U V
  change LinearMap.det (e.symm.toLinearEquiv.toLinearMap ∘ₗ
    ((fderiv ℝ f p.fst).toLinearMap.prodMap (fderiv ℝ g p.snd).toLinearMap) ∘ₗ
      e.toLinearEquiv.toLinearMap)=_
  exact (LinearMap.det_conj _ e.toLinearEquiv.symm).trans (LinearMap.det_prodMap _ _)

end ProductDerivative

abbrev PairChart (n : ℕ) := WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))

def pairChartDomain (n : ℕ) : Set (PairChart n) :=
  {p | ‖p.fst‖ < 2 ∧ ‖p.snd‖ < 2}

def pairChartGamma {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (p : PairChart n) :
    EuclideanDisorder (n+1) P →L[ℝ] PairChart n :=
  pairHilbert (chartGamma n c p.fst) (chartGamma n c p.snd)

lemma pairChartDomain_isOpen (n : ℕ) : IsOpen (pairChartDomain n) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
  exact (isOpen_lt e.continuous.fst.norm continuous_const).inter
    (isOpen_lt e.continuous.snd.norm continuous_const)

lemma pairChartGamma_contDiffOn {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    ContDiffOn ℝ 1 (pairChartGamma n c) (pairChartDomain n) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
  apply contDiffOn_clm_apply.mpr
  intro g
  have hf := (chartGamma_contDiffOn n c).comp e.contDiff.fst.contDiffOn
    (fun (p : PairChart n) (hp : p ∈ pairChartDomain n) => show p.fst ∈ ball 0 2 by simpa using hp.1)
  have hs := (chartGamma_contDiffOn n c).comp e.contDiff.snd.contDiffOn
    (fun (p : PairChart n) (hp : p ∈ pairChartDomain n) => show p.snd ∈ ball 0 2 by simpa using hp.2)
  exact e.symm.contDiff.comp_contDiffOn
    ((hf.clm_apply contDiffOn_const).prodMk (hs.clm_apply contDiffOn_const))

lemma pairChartGamma_zero_iff {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (p : PairChart n) (g : EuclideanDisorder (n+1) P) :
    pairChartGamma n c p g=0 ↔ chartGamma n c p.fst g=0 ∧ chartGamma n c p.snd g=0 := by
  change WithLp.toLp 2 (chartGamma n c p.fst g,chartGamma n c p.snd g)=WithLp.toLp 2 (0,0) ↔ _
  rw [(WithLp.toLp_injective 2).eq_iff,Prod.mk.injEq]

/-- The actual derivative is block diagonal because each observed gradient
is differentiated in its own actual spatial variable. -/
theorem pair_spatialJacobian_det {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (g : EuclideanDisorder (n+1) P) {p : PairChart n} (hp : p ∈ pairChartDomain n) :
    (spatialJacobian (pairChartGamma n c) g p).det =
      (spatialJacobian (chartGamma n c) g p.fst).det *
        (spatialJacobian (chartGamma n c) g p.snd).det := by
  have hf := (((chartGamma_contDiffOn n c).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hp.1))).clm_apply
      (contDiffAt_const (c := g))).differentiableAt_one
  have hs := (((chartGamma_contDiffOn n c).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hp.2))).clm_apply
      (contDiffAt_const (c := g))).differentiableAt_one
  exact hilbert_product_derivative_det (fun u => chartGamma n c u g)
    (fun u => chartGamma n c u g) p hf hs

/-- Literal coordinate zeros are simultaneous intrinsic critical points. -/
theorem pairChartGamma_intrinsic_zero_iff {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    {p : PairChart n} (hp : p ∈ pairChartDomain n) (J : Disorder (n+1) P) :
    pairChartGamma n c p (euclideanDisorder J)=0 ↔
      surfaceGradient (field c J) (manuscriptChart n p.fst)=0 ∧
      surfaceGradient (field c J) (manuscriptChart n p.snd)=0 := by
  rw [pairChartGamma_zero_iff]
  have h1 := chartGamma_zero_iff_derivative_zero n c hp.1 (euclideanDisorder J)
  have h2 := chartGamma_zero_iff_derivative_zero n c hp.2 (euclideanDisorder J)
  simp only [unpack_euclideanDisorder] at h1 h2
  rw [h1,h2,actual_field_chart_critical_iff c J hp.1,actual_field_chart_critical_iff c J hp.2]

/-- Adjoint surjectivity of an actual continuous linear equivalence. -/
lemma adjoint_equiv_surjective {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃L[ℝ] F) : Surjective (e : E →L[ℝ] F).adjoint := by
  intro v
  refine ⟨(e.symm : F →L[ℝ] E).adjoint v,?_⟩
  have he : (e.symm : F →L[ℝ] E).comp (e : E →L[ℝ] F)=ContinuousLinearMap.id ℝ E := by
    ext u
    exact e.symm_apply_apply u
  have h := congrArg (fun L : E →L[ℝ] E => L.adjoint v) he
  simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using h

/-- The genuine chart gradient is an invertible change of complete tangent
frame coordinates, for every original coefficient vector. -/
def chartFrameMap {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < 2) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (chartTangentEquiv u hu : EuclideanSpace ℝ (Fin n) →L[ℝ]
    tangentPlane (manuscriptChart n u)).adjoint.comp
      (tangentBasis (manuscriptChart n u) (manuscriptChart_norm_sq hu)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma chartFrameMap_surjective {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < 2) :
    Surjective (chartFrameMap u hu) :=
  (adjoint_equiv_surjective (chartTangentEquiv u hu)).comp
    (tangentBasis (manuscriptChart n u) (manuscriptChart_norm_sq hu)).repr.symm.surjective

lemma chartGamma_eq_frame {n P : ℕ} (c : Degree P → ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < 2) (g : EuclideanDisorder (n+1) P) :
    chartGamma n c u g=chartFrameMap u hu
      (gradientCLM c (manuscriptChart n u)
        (tangentFrame (manuscriptChart n u) (manuscriptChart_norm_sq hu)) g) := by
  rw [tangentFrame_gradient_eq,chartFrameMap,ContinuousLinearMap.comp_apply]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply]
  rw [chartGamma_eq_adjoint_intrinsic c hu]
  rfl

/-- Actual pair chart gradients are surjective on a dimension-independent
small-overlap neighborhood. The proof uses the already proved genuine
value/tangent covariance, so it covers both pure and nonpure mixtures. -/
theorem uniform_pairChartGamma_surjective (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 : ℝ,0 < ρ0 ∧ ∀ (n : ℕ) (p : PairChart n),p ∈ pairChartDomain n →
      |overlap (manuscriptChart n p.fst) (manuscriptChart n p.snd)| ≤ ρ0 →
      Surjective (pairChartGamma n (centerCoefficients (mixtureCoefficients μ) Q) p) := by
  obtain ⟨ρ0,δ,hρ0,hδ,hpair⟩ := PairObservationSmallOverlap.uniform_value_pair_nondegenerate μ hQ hdeg
  refine ⟨ρ0,hρ0,?_⟩
  intro n p hp hr z
  let x := manuscriptChart n p.fst
  let y := manuscriptChart n p.snd
  have hx : ‖x‖^2=(n+1:ℕ) := manuscriptChart_norm_sq hp.1
  have hy : ‖y‖^2=(n+1:ℕ) := manuscriptChart_norm_sq hp.2
  obtain ⟨u,hu⟩ := chartFrameMap_surjective p.fst hp.1 z.fst
  obtain ⟨v,hv⟩ := chartFrameMap_surjective p.snd hp.2 z.snd
  have hsurj := (hpair (n+1) n (by omega) x y hx hy
    (tangentFrame x hx) (tangentFrame y hy) (tangentFrame_orthonormal x hx)
    (tangentFrame_orthonormal y hy) (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr).2.1
  obtain ⟨g,hg⟩ := hsurj (WithLp.toLp 2 (WithLp.toLp 2 (0,u),WithLp.toLp 2 (0,v)))
  have hgu : gradientCLM _ x (tangentFrame x hx) g=u := congrArg (fun w => w.fst.snd) hg
  have hgv : gradientCLM _ y (tangentFrame y hy) g=v := congrArg (fun w => w.snd.snd) hg
  refine ⟨g,?_⟩
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change chartGamma n _ p.fst g=z.fst
    rw [chartGamma_eq_frame _ _ hp.1,hgu,hu]
  · change chartGamma n _ p.snd g=z.snd
    rw [chartGamma_eq_frame _ _ hp.2,hgv,hv]

end SlowEquilibration.SphericalPairChartGeometry
