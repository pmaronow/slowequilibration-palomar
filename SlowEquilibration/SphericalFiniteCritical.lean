-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMorse

/-! Finiteness of the literal critical set of the actual spherical field. -/

@[expose] public section

namespace SlowEquilibration.SphericalMorse

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphereHessian SlowEquilibration.SphericalKacRiceGluing
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.GaussianLocalCoordinates
open SlowEquilibration.SphericalIntrinsicKacRice
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual chart inverse, on the ambient space; continuous away from its
omitted pole when restricted to the actual sphere. -/
def manuscriptChartInverse (n : ℕ) (x : Vector (n+1)) : EuclideanSpace ℝ (Fin n) :=
  sphereChartInvND ((radiusHomeomorph n).symm x)

theorem manuscriptChartInverse_left_inv {n : ℕ} {u : EuclideanSpace ℝ (Fin n)}
    (hu : ‖u‖ < 2) : manuscriptChartInverse n (manuscriptChart n u) = u := by
  change sphereChartInvND ((radiusHomeomorph n).symm
    (radiusHomeomorph n (sphereChartND u))) = u
  rw [(radiusHomeomorph n).symm_apply_apply, sphereChartND_left_inv hu]

theorem manuscriptChartInverse_continuousAt_chart {n : ℕ} {u : EuclideanSpace ℝ (Fin n)}
    (hu : ‖u‖ < 2) : ContinuousAt (manuscriptChartInverse n) (manuscriptChart n u) := by
  have hw : ContinuousAt (sphereChartInvND : ChartAmbient n → EuclideanSpace ℝ (Fin n))
      (sphereChartND u) := by
    have hfst := (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).continuous.fst
    have hsnd := (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).continuous.snd
    have hpos : 0 < (1 + (WithLp.ofLp (sphereChartND u)).2) / 2 := by
      linarith [sphereChartND_snd_gt_neg_one hu]
    exact (((continuous_const.add hsnd).div_const 2).sqrt.continuousAt.inv₀
      (Real.sqrt_pos.mpr hpos).ne').smul hfst.continuousAt
  have hx : (radiusHomeomorph n).symm (manuscriptChart n u) = sphereChartND u := by
    change (radiusHomeomorph n).symm (radiusHomeomorph n (sphereChartND u)) = _
    exact (radiusHomeomorph n).symm_apply_apply _
  have hw' : ContinuousAt sphereChartInvND
      ((radiusHomeomorph n).symm (manuscriptChart n u)) := by
    rw [hx]
    exact hw
  exact hw'.comp (radiusHomeomorph n).symm.continuous.continuousAt

/-- Compactness uses the literal sphere and the continuous actual tangential
gradient, with no random or surrogate compact set. -/
theorem sphereCriticalSet_isCompact {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) : IsCompact (sphereCriticalSet n c J) := by
  have he : {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ)} =
      sphere 0 (Real.sqrt (n+1 : ℕ)) := by
    ext x
    simp only [mem_ofPred_eq, mem_sphere, dist_zero_right]
    constructor
    · intro h
      nlinarith [norm_nonneg x, Real.sqrt_nonneg (n+1 : ℕ),
        Real.sq_sqrt (Nat.cast_nonneg (n+1))]
    · intro h
      rw [h, Real.sq_sqrt (Nat.cast_nonneg (n+1))]
  change IsCompact ({x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ)} ∩
    {x | surfaceGradient (field c J) x = 0})
  rw [he]
  exact (isCompact_sphere 0 _).inter_right
    (isClosed_eq (field_surfaceGradient_contDiff c J).continuous continuous_const)

/-- If the actual chart zeros are regular and the omitted pole is noncritical,
compactness of the true sphere forces its literal critical set to be finite. -/
theorem sphereCriticalSet_finite_of_chart_regular {P : ℕ} (n : ℕ)
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (hpole : surfaceGradient (field c J) (southPole n) ≠ 0)
    (hreg : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < 2 →
      surfaceGradient (field c J) (manuscriptChart n u) = 0 →
      (actualChartHessian n c J u).det ≠ 0) :
    (sphereCriticalSet n c J).Finite := by
  let S := sphereCriticalSet n c J
  let K := manuscriptChartInverse n '' S
  have hex (x : Vector (n+1)) (hx : x ∈ S) :
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ < 2 ∧ manuscriptChart n u = x := by
    have hxp : x ≠ southPole n := fun he => hpole (he ▸ hx.2)
    have hm : x ∈ manuscriptChart n '' ball 0 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨hx.1, hxp⟩
    obtain ⟨u, hu, he⟩ := hm
    exact ⟨u, by simpa using hu, he⟩
  have hcontinuous : ContinuousOn (manuscriptChartInverse n) S := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hex x hx
    exact (manuscriptChartInverse_continuousAt_chart hu).continuousWithinAt
  have hcompact : IsCompact K := (sphereCriticalSet_isCompact n c J).image_of_continuousOn hcontinuous
  have hK (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ K) :
      ‖u‖ < 2 ∧ manuscriptChart n u ∈ S := by
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨v, hv, rfl⟩ := hex x hx
    rw [manuscriptChartInverse_left_inv hv]
    exact ⟨hv, hx⟩
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun u => chartGamma n c u (euclideanDisorder J)
  have hf : ContDiffOn ℝ 1 f (ball 0 2) :=
    (chartGamma_contDiffOn n c).clm_apply contDiffOn_const
  have hfinite : K.Finite := compact_set_of_regular_zeros_finite f (ball 0 2) isOpen_ball hf
    K hcompact (fun u hu => by simpa using (hK u hu).1) (by
      intro u hu
      dsimp only [f]
      rw [chartGamma_zero_iff_derivative_zero n c (hK u hu).1, unpack_euclideanDisorder]
      exact (actual_field_chart_critical_iff c J (hK u hu).1).mpr (hK u hu).2.2) (by
      intro u hu
      exact hreg u (hK u hu).1 (hK u hu).2.2)
  apply hfinite.of_finite_image
  intro x hx y hy he
  obtain ⟨u, hu, rfl⟩ := hex x hx
  obtain ⟨v, hv, rfl⟩ := hex y hy
  rw [manuscriptChartInverse_left_inv hu, manuscriptChartInverse_left_inv hv] at he
  exact congrArg (manuscriptChart n) he

/-- The actual full tensor Gaussian field has finitely many intrinsic sphere
critical points almost surely; no Morse or finite-count hypothesis is assumed. -/
theorem actual_sphere_criticalSet_finite_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree, (sphereCriticalSet n c J).Finite := by
  filter_upwards [actual_chart_regular_ae n μ hQ,
    fixed_point_noncritical_ae n hn μ hQ (southPole n) (southPole_norm_sq n)] with J hJ hpole
  exact sphereCriticalSet_finite_of_chart_regular n _ J hpole hJ

/-- Every finite-valued mark gives a finite literal critical-point sum whenever
the actual critical set is finite. -/
theorem actualSphereCount_lt_top_of_finite {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (hfinite : (sphereCriticalSet n c J).Finite)
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞)
    (hpsi : ∀ x ∈ sphereCriticalSet n c J, psi J x < ⊤) :
    actualSphereCount n c psi J < ⊤ := by
  classical
  letI : Fintype (sphereCriticalSet n c J) := hfinite.fintype
  change (∑' x : sphereCriticalSet n c J, psi J x) < ⊤
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr (fun x _ => hpsi x x.property)

/-- In particular, the genuine unmarked number of intrinsic critical points
is finite almost surely under the original Gaussian tensor law. -/
theorem actual_sphere_count_lt_top_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree, actualSphereCount n c (fun _ _ => 1) J < ⊤ := by
  filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ] with J hJ
  exact actualSphereCount_lt_top_of_finite n _ J hJ _ (fun _ _ => by simp)

/-- The actual mixed spherical field is Morse and has a finite literal
critical set simultaneously, with all assumptions discharged from the model. -/
theorem actual_sphere_morse_finite_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      (sphereCriticalSet n c J).Finite ∧
      (∀ x ∈ sphereCriticalSet n c J, (intrinsicHessian (field c J) x).det ≠ 0) ∧
      actualSphereCount n c (fun _ _ => 1) J < ⊤ := by
  filter_upwards [actual_sphere_criticalSet_finite_ae n hn μ hQ,
    actual_sphere_morse_ae n hn μ hQ, actual_sphere_count_lt_top_ae n hn μ hQ] with J hf hm hc
  exact ⟨hf, hm, hc⟩

end
end SlowEquilibration.SphericalMorse
