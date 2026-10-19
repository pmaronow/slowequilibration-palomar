-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalChartGeometry
public import SlowEquilibration.SphereNoAtoms
public import SlowEquilibration.RoundSphereVolume

@[expose] public section

/-!
# Genuine global sphere counts from the ordinary round chart

The one-chart coordinate domain covers the actual sphere except its south
pole. Its missing point has actual round volume zero. The global count below
is the literal sum over the actual tangential-gradient zeros on the actual
radius sphere, and is identified with the actual chart count whenever the
omitted point is noncritical.
-/

noncomputable section
namespace SlowEquilibration.SphericalKacRiceGluing

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphericalChartGeometry
open SlowEquilibration.SphericalGaussianJet
open scoped Topology ENNReal RealInnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev ChartAmbient (n : ℕ) := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)

def unitSouthPole (n : ℕ) : ChartAmbient n := WithLp.toLp 2 (0,(-1 : ℝ))

def radiusHomeomorph (n : ℕ) : ChartAmbient n ≃ₜ Vector (n+1) :=
  (chartAmbientIsometry n).toHomeomorph.trans
    (Homeomorph.smulOfNeZero (Real.sqrt (n+1 : ℕ)) (Real.sqrt_pos.mpr (by positivity)).ne')

def southPole (n : ℕ) : Vector (n+1) := radiusHomeomorph n (unitSouthPole n)

@[simp] theorem radiusHomeomorph_apply (n : ℕ) (w : ChartAmbient n) :
    radiusHomeomorph n w = Real.sqrt (n+1 : ℕ) • chartAmbientIsometry n w := rfl

theorem radiusHomeomorph_norm_sq (n : ℕ) (w : ChartAmbient n) :
    ‖radiusHomeomorph n w‖^2 = (n+1 : ℕ)*‖w‖^2 := by
  simp only [radiusHomeomorph_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    (chartAmbientIsometry n).norm_map,Real.sq_sqrt (Nat.cast_nonneg (n+1))]

@[simp] theorem unitSouthPole_norm (n : ℕ) : ‖unitSouthPole n‖ = 1 := by
  have h : ‖unitSouthPole n‖^2 = 1 := by
    rw [unitSouthPole,WithLp.prod_norm_sq_eq_of_L2]
    simp
  nlinarith [norm_nonneg (unitSouthPole n)]

theorem southPole_norm_sq (n : ℕ) : ‖southPole n‖^2 = (n+1 : ℕ) := by
  rw [southPole,radiusHomeomorph_norm_sq,unitSouthPole_norm]
  ring

theorem unit_south_iff_snd_eq {n : ℕ} {w : ChartAmbient n} (hw : ‖w‖ = 1) :
    w = unitSouthPole n ↔ (WithLp.ofLp w).2 = -1 := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro ht
    have he := WithLp.prod_norm_sq_eq_of_L2 w
    rw [hw] at he
    change (1 : ℝ)^2=‖(WithLp.ofLp w).1‖^2+‖(WithLp.ofLp w).2‖^2 at he
    simp only [Real.norm_eq_abs,sq_abs] at he
    rw [ht] at he
    have hf : (WithLp.ofLp w).1 = 0 := by
      have hfs : ‖(WithLp.ofLp w).1‖^2 = 0 := by
        nlinarith
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (WithLp.ofLp w).1])
    apply WithLp.ofLp_injective 2
    exact Prod.ext hf ht

theorem sphereChartND_image_ball_except_pole (n : ℕ) :
    sphereChartND '' ball (0 : EuclideanSpace ℝ (Fin n)) 2 =
      {w : ChartAmbient n | ‖w‖ = 1 ∧ w ≠ unitSouthPole n} := by
  rw [sphereChartND_image_ball]
  ext w
  constructor
  · rintro ⟨hw,ht⟩
    refine ⟨hw,?_⟩
    intro he
    have h := (unit_south_iff_snd_eq hw).mp he
    linarith
  · rintro ⟨hw,hne⟩
    refine ⟨hw,?_⟩
    have he := WithLp.prod_norm_sq_eq_of_L2 w
    rw [hw] at he
    change (1 : ℝ)^2=‖(WithLp.ofLp w).1‖^2+‖(WithLp.ofLp w).2‖^2 at he
    simp only [Real.norm_eq_abs,sq_abs] at he
    have ht : -1 ≤ (WithLp.ofLp w).2 := by
      nlinarith [sq_nonneg ‖(WithLp.ofLp w).1‖]
    have hn : (WithLp.ofLp w).2 ≠ -1 := fun h => hne ((unit_south_iff_snd_eq hw).mpr h)
    exact lt_of_le_of_ne ht hn.symm

/-- Exact genuine-radius chart coverage; no atlas-cover hypothesis is used. -/
theorem manuscriptChart_image_ball_except_pole (n : ℕ) :
    manuscriptChart n '' ball (0 : EuclideanSpace ℝ (Fin n)) 2 =
      {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧ x ≠ southPole n} := by
  have hN : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hu' : ‖u‖ < 2 := by simpa using hu
    refine ⟨manuscriptChart_norm_sq hu',?_⟩
    intro he
    have hp : sphereChartND u = unitSouthPole n := (radiusHomeomorph n).injective he
    have hmem : sphereChartND u ∈ sphereChartND '' ball (0 : EuclideanSpace ℝ (Fin n)) 2 :=
      ⟨u,hu,rfl⟩
    rw [sphereChartND_image_ball_except_pole] at hmem
    exact hmem.2 hp
  · rintro ⟨hx,hne⟩
    let w := (radiusHomeomorph n).symm x
    have hwx : radiusHomeomorph n w = x := (radiusHomeomorph n).apply_symm_apply x
    have hw : ‖w‖ = 1 := by
      have he := radiusHomeomorph_norm_sq n w
      rw [hwx,hx] at he
      have hs : ‖w‖^2=1 := mul_left_cancel₀ hN.ne' (by simpa only [mul_one] using he.symm)
      nlinarith [norm_nonneg w]
    have hwp : w ≠ unitSouthPole n := by
      intro he
      apply hne
      rw [← hwx,he]
      rfl
    have hm : w ∈ sphereChartND '' ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
      rw [sphereChartND_image_ball_except_pole]
      exact ⟨hw,hwp⟩
    obtain ⟨u,hu,he⟩ := hm
    refine ⟨u,hu,?_⟩
    change radiusHomeomorph n (sphereChartND u) = x
    rw [he,hwx]

theorem manuscriptChart_injOn (n : ℕ) :
    InjOn (manuscriptChart n) (ball (0 : EuclideanSpace ℝ (Fin n)) 2) := by
  intro u hu v hv he
  apply sphereChartND_injOn hu hv
  exact (radiusHomeomorph n).injective he

/-- The true global marked count on the actual sphere and actual disorder. -/
def actualSphereCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+1) P) : ℝ≥0∞ :=
  ∑' x : {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧ surfaceGradient (field c J) x=0}, psi J x

/-- The genuine chart bijection identifies literal intrinsic sphere zeros
with literal scalar coordinate critical points when the omitted pole is
noncritical. This equality also holds for infinite nonnegative marked counts. -/
theorem actualSphereCount_eq_chart_of_noncritical_pole {P : ℕ}
    (n : ℕ) (c : Degree P → ℝ) (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞)
    (J : Disorder (n+1) P) (hpole : surfaceGradient (field c J) (southPole n) ≠ 0) :
    actualSphereCount n c psi J = actualChartCount n c (fun J u => psi J (manuscriptChart n u)) J := by
  classical
  let C := {u : EuclideanSpace ℝ (Fin n) | u ∈ ball 0 2 ∧
    fderiv ℝ (fun y => field c J (manuscriptChart n y)) u=0}
  let S := {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧ surfaceGradient (field c J) x=0}
  let f : C → S := fun u => ⟨manuscriptChart n u,
    manuscriptChart_norm_sq (by simpa using u.property.1),
    (actual_field_chart_critical_iff c J (by simpa using u.property.1)).mp u.property.2⟩
  have hi : Injective f := by
    intro u v he
    apply Subtype.ext
    exact manuscriptChart_injOn n u.property.1 v.property.1 (congrArg Subtype.val he)
  have hs : Surjective f := by
    intro x
    have hxp : (x : Vector (n+1)) ≠ southPole n := by
      intro he
      apply hpole
      rw [← he]
      exact x.property.2
    have hx : (x : Vector (n+1)) ∈ manuscriptChart n '' ball (0 : EuclideanSpace ℝ (Fin n)) 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨x.property.1,hxp⟩
    obtain ⟨u,hu,he⟩ := hx
    have hz : fderiv ℝ (fun y => field c J (manuscriptChart n y)) u=0 := by
      apply (actual_field_chart_critical_iff c J (by simpa using hu)).mpr
      rw [he]
      exact x.property.2
    exact ⟨⟨u,hu,hz⟩,Subtype.ext he⟩
  let e : C ≃ S := Equiv.ofBijective f ⟨hi,hs⟩
  exact (e.tsum_eq (fun x : S => psi J x)).symm

/-- The single omitted point is null under the independently constructed
actual round volume. This is derived from genuine cone-volume non-atomicity. -/
theorem manuscriptRoundVolume_southPole_zero (n : ℕ) (hn : 1 ≤ n) :
    manuscriptRoundVolume n {southPole n} = 0 := by
  have hpre : (radiusHomeomorph n) ⁻¹' {southPole n} = {unitSouthPole n} := by
    ext w
    change radiusHomeomorph n w=southPole n ↔ w=unitSouthPole n
    exact (radiusHomeomorph n).injective.eq_iff
  let v : sphere (0 : ChartAmbient n) 1 := ⟨unitSouthPole n,by
    simpa only [mem_sphere,dist_zero_right] using unitSouthPole_norm n⟩
  have hpre' : (Subtype.val : sphere (0 : ChartAmbient n) 1 → ChartAmbient n) ⁻¹'
      {unitSouthPole n} = {v} := by
    ext w
    change (w : ChartAmbient n)=unitSouthPole n ↔ w=v
    constructor
    · intro h
      apply Subtype.ext
      exact h
    · intro h
      exact congrArg Subtype.val h
  have hdim : 2 ≤ Module.finrank ℝ (ChartAmbient n) := by
    rw [chartAmbient_finrank]
    omega
  change (radiusAreaScale n • Measure.map (radiusHomeomorph n) (sphereAreaND n)) {southPole n}=0
  rw [Measure.smul_apply,Measure.map_apply (radiusHomeomorph n).continuous.measurable (measurableSet_singleton _)]
  change radiusAreaScale n*sphereAreaND n ((radiusHomeomorph n) ⁻¹' {southPole n})=0
  rw [hpre,sphereAreaND,Measure.map_apply measurable_subtype_coe (measurableSet_singleton _),
    hpre',SphereVolume.angular_singleton_zero hdim v,mul_zero]

/-- Actual round volume is supported on the actual radius sphere. -/
theorem manuscriptRoundVolume_onSphere (n : ℕ) :
    ∀ᵐ x ∂manuscriptRoundVolume n, ‖x‖^2=(n+1 : ℕ) := by
  have harea : ∀ᵐ w ∂sphereAreaND n, ‖w‖=1 := by
    unfold sphereAreaND
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
    exact ae_of_all _ fun w => by simpa only [mem_sphere,dist_zero_right] using w.property
  have hmap : ∀ᵐ x ∂(sphereAreaND n).map (radiusHomeomorph n), ‖x‖^2=(n+1 : ℕ) := by
    apply (ae_map_iff (radiusHomeomorph n).continuous.measurable.aemeasurable
      (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
    filter_upwards [harea] with w hw
    rw [radiusHomeomorph_norm_sq,hw]
    ring
  exact Measure.ae_smul_measure hmap (radiusAreaScale n)

/-- Removing the omitted pole leaves the independently constructed actual
round volume unchanged; no full-sphere chart assumption is used. -/
theorem manuscriptRoundVolume_restrict_full_chart (n : ℕ) (hn : 1 ≤ n) :
    (manuscriptRoundVolume n).restrict
      (manuscriptChart n '' ball (0 : EuclideanSpace ℝ (Fin n)) 2) = manuscriptRoundVolume n := by
  have hne : ∀ᵐ x ∂manuscriptRoundVolume n, x ≠ southPole n := by
    rw [ae_iff]
    have hs : {x : Vector (n+1) | ¬x ≠ southPole n}={southPole n} := by
      ext x
      simp only [mem_ofPred_eq,mem_singleton_iff,ne_eq,not_not]
    rw [hs]
    exact manuscriptRoundVolume_southPole_zero n hn
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [manuscriptRoundVolume_onSphere n,hne] with x hx hne
  rw [manuscriptChart_image_ball_except_pole]
  exact ⟨hx,hne⟩

/-- The global count is literally the actual chart count almost surely when
the actual omitted pole is almost surely noncritical. This geometric transfer
is kept separate from the Gaussian noncritical-point theorem. -/
theorem actualSphereCount_ae_eq_chart {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞)
    (hpole : ∀ᵐ J ∂disorderLaw (n+1) P, surfaceGradient (field c J) (southPole n) ≠ 0) :
    actualSphereCount n c psi =ᵐ[disorderLaw (n+1) P]
      actualChartCount n c (fun J u => psi J (manuscriptChart n u)) := by
  filter_upwards [hpole] with J hJ
  exact actualSphereCount_eq_chart_of_noncritical_pole n c psi J hJ

/-- Actual global marked count transferred to the original-tensor-law chart
Kac--Rice formula. The single noncritical-pole input can be discharged by the
true positive-dimensional tangent-gradient Gaussian law. -/
theorem actual_tensor_sphere_chart_kacRice_of_noncritical_pole
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2)
    (hpole : ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree,
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) (southPole n) ≠ 0) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualSphereCount n c psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫⁻ J, actualSphereCount n c psi J ∂disorderLaw (n+1) μ.maxDegree) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (chartGamma n c u) 0 *
        ∫⁻ J, ENNReal.ofReal |(actualChartHessian n c J u).det| * psi J (manuscriptChart n u)
          ∂WholeFieldRegression.coefficientKernel (chartGamma n c u) 0 := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hmchart : Measurable (manuscriptChart n) := by
    unfold manuscriptChart
    exact (((chartAmbientIsometry n).continuous.comp sphereChartND_continuous).const_smul
      (Real.sqrt (n+1 : ℕ))).measurable
  have hm : Measurable fun p : Disorder (n+1) μ.maxDegree × EuclideanSpace ℝ (Fin n) =>
      psi p.1 (manuscriptChart n p.2) :=
    hpsi.comp (measurable_fst.prodMk (hmchart.comp measurable_snd))
  have hk := actual_tensor_chart_kacRice n μ hQ (fun J u => psi J (manuscriptChart n u)) hm
  have he := actualSphereCount_ae_eq_chart n c psi hpole
  exact ⟨hk.1.congr he.symm,(lintegral_congr_ae he).trans hk.2⟩

end SlowEquilibration.SphericalKacRiceGluing
