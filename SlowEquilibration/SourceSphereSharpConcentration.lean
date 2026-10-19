-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeCenterMean
public import SlowEquilibration.EntranceLatitudeTangentObservable
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceCutoff
public import SlowEquilibration.ConditionedEntrancePhysicalCutoffEnergy
public import SlowEquilibration.EntranceActualSourceCutoffTiltMoments
public import SlowEquilibration.ConditionedEntrancePureRegularGradient
public import SlowEquilibration.ConditionedEntrancePureCutoffEnergy
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The curvature logarithmic Sobolev input in Section 8 is kept as an
explicit literature proposition. The Herbst argument, including both signs
of the parameter, is proved here. It gives the exact manuscript sphere
constant and the error-free latitude bound for the actual center gradient.
The input is the exponential specialization of the sphere logarithmic
Sobolev inequality, extended to Lipschitz functions. Its source is
Bakry--Gentil--Ledoux, Analysis and Geometry of Markov Diffusion Operators
(2014), Proposition 5.7.1 and Section 5.4; DOI 10.1007/978-3-319-00227-9.
The original curvature criterion and sphere normalization are in
Bakry--Émery (1985), Corollary 2, p. 199, and sphere example (b), p. 200:
https://www.numdam.org/item/SPS_1985__19__177_0.pdf.
It does not assume the concentration conclusion or a spin-glass estimate.
The deterministic mixed and proper-pure cutoff value and gradient
estimates are also proved with constants independent of the cutoff scale. The joint
latitude theorem uses the repository's original Gaussian-bank good event;
its identification with the manuscript's harmonic event remains separate.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceSphereSharpConcentration

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet EntranceLatitudeTangentObservable
open scoped Topology RealInnerProductSpace NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Normalized surface probability on the unit sphere, obtained by the
canonical radius dilation of the repository's normalized sphere law. -/
def unitSphereLaw (n : ℕ) : Measure (Vector n) :=
  (sphereLaw n).map (fun x => (Real.sqrt (n : ℝ))⁻¹ • x)

instance unitSphereLaw_probability (n : ℕ) : IsProbabilityMeasure (unitSphereLaw n) := by
  unfold unitSphereLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

private theorem unitSphereLaw_support {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ x ∂unitSphereLaw n, ‖x‖ = 1 := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  rw [unitSphereLaw]
  apply (ae_map_iff (by fun_prop : Measurable (fun x : Vector n =>
    (Real.sqrt (n : ℝ))⁻¹ • x)).aemeasurable
    ((isClosed_eq continuous_norm continuous_const).measurableSet)).mpr
  filter_upwards [sphereLaw_support hn] with x hx
  have hx' : ‖x‖ = Real.sqrt (n : ℝ) :=
    (Real.sqrt_sq (norm_nonneg x)).symm.trans (congrArg Real.sqrt hx)
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hx', hs.ne']

/-- The literal geodesic Lipschitz condition on the unit sphere. Values
away from the sphere are irrelevant to the surface probability. -/
def GeodesicLipschitz {n : ℕ} (g : Vector n → ℝ) (L : ℝ) : Prop :=
  ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 →
    |g x - g y| ≤ L * Real.arccos (inner ℝ x y)

/-- The exponential specialization `q = exp(t*g)` of the curvature
logarithmic Sobolev inequality. The ambient dimension is `n`, so the
unit sphere has Ricci curvature `n-2`. Lipschitz extension by smooth
approximation belongs to this explicit literature input. -/
def BakryEmerySphereLogSobolev : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (g : Vector n → ℝ) (L : ℝ), 0 ≤ L →
    GeodesicLipschitz g L → ∀ t : ℝ,
    (∫ x, Real.exp (t * g x) * (t * g x) ∂unitSphereLaw n) -
      mgf g (unitSphereLaw n) t * Real.log (mgf g (unitSphereLaw n) t) ≤
      (L ^ 2 * t ^ 2 / (2 * ((n : ℝ) - 2))) * mgf g (unitSphereLaw n) t

private theorem geodesic_continuousOn {n : ℕ} {g : Vector n → ℝ} {L : ℝ}
    (hg : GeodesicLipschitz g L) : ContinuousOn g {x | ‖x‖ = 1} := by
  intro x hx
  have hxn : ‖x‖ = 1 := hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh : Tendsto (fun y : Vector n => L * Real.arccos (inner ℝ y x))
      (𝓝[{x | ‖x‖ = 1}] x) (𝓝 0) := by
    have hc : Continuous (fun y : Vector n => L * Real.arccos (inner ℝ y x)) := by
      fun_prop
    simpa [real_inner_self_eq_norm_sq, hxn] using
      (hc.continuousAt (x := x)).tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hh
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa only [Real.norm_eq_abs] using hg y x hy hx

private theorem geodesic_ae_bounded {n : ℕ} (hn : 1 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L) :
    AEStronglyMeasurable g (unitSphereLaw n) ∧
      ∃ B : ℝ, ∀ᵐ x ∂unitSphereLaw n, |g x| ≤ B := by
  have hc := geodesic_continuousOn hg
  have hset : {x : Vector n | ‖x‖ = 1} = Metric.sphere 0 1 := by
    ext x
    simp
  have hm : MeasurableSet {x : Vector n | ‖x‖ = 1} := by
    rw [hset]
    exact Metric.isClosed_sphere.measurableSet
  have hrestrict : (unitSphereLaw n).restrict {x | ‖x‖ = 1} = unitSphereLaw n :=
    Measure.restrict_eq_self_of_ae_mem (unitSphereLaw_support hn)
  constructor
  · simpa only [hrestrict] using hc.aestronglyMeasurable (μ := unitSphereLaw n) hm
  · obtain ⟨B, hB⟩ := (show IsCompact {x : Vector n | ‖x‖ = 1} by
      rw [hset]; exact isCompact_sphere 0 1).exists_bound_of_continuousOn hc
    exact ⟨B, (unitSphereLaw_support hn).mono (fun x hx => by
      simpa only [Real.norm_eq_abs] using hB x hx)⟩

private theorem bounded_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hg : AEStronglyMeasurable g μ) {B : ℝ} (hB : ∀ᵐ x ∂μ, |g x| ≤ B)
    (t : ℝ) : Integrable (fun x => Real.exp (t * g x)) μ := by
  apply Integrable.of_bound (by fun_prop) (Real.exp (|t| * B))
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((abs_mul t (g x)).le.trans
    (mul_le_mul_of_nonneg_left hx (abs_nonneg t)))

/-- The scalar Herbst argument. This is ordinary real calculus; no
functional inequality or probabilistic input is hidden in the proof. -/
theorem herbst_of_log_mgf_differential {ψ ψ' : ℝ → ℝ} {a b : ℝ}
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hzero : ψ 0 = 0) (hmean : ψ' 0 = b)
    (hent : ∀ t, t * ψ' t - ψ t ≤ a * t ^ 2) (t : ℝ) :
    ψ t ≤ b * t + a * t ^ 2 := by
  let F : ℝ → ℝ := fun s => dslope ψ 0 s - a * s
  have hc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro s
    apply ContinuousAt.sub _ (by fun_prop)
    by_cases hs : s = 0
    · subst s
      exact continuousAt_dslope_same.mpr (hψ 0).differentiableAt
    · exact (continuousAt_dslope_of_ne hs).mpr (hψ s).continuousAt
  have hd (s : ℝ) (hs : s ≠ 0) :
      HasDerivAt F ((s * ψ' s - ψ s) / s ^ 2 - a) s := by
    have hq := ((hψ s).div (hasDerivAt_id s) hs).sub
      ((hasDerivAt_id s).const_mul a)
    have he : F =ᶠ[𝓝 s] (fun z => ψ z / z - a * z) := by
      filter_upwards [dslope_eventuallyEq_slope_of_ne ψ hs] with z hz
      simp only [F, hz, slope_def_field, sub_zero, hzero]
    convert hq.congr_of_eventuallyEq he using 1
    simp only [id_eq, mul_one]
    ring
  have hdle (s : ℝ) (hs : s ≠ 0) : deriv F s ≤ 0 := by
    rw [(hd s hs).deriv]
    have hsq : 0 < s ^ 2 := sq_pos_of_ne_zero hs
    have hb := (div_le_iff₀ hsq).mpr (hent s)
    linarith
  have he : t * dslope ψ 0 t = ψ t := by
    simpa only [sub_zero, smul_eq_mul, hzero] using sub_smul_dslope ψ 0 t
  have hF0 : F 0 = b := by simp [F, dslope_same, (hψ 0).deriv, hmean]
  rcases le_total 0 t with ht | ht
  · have hm : AntitoneOn F (Ici 0) := antitoneOn_of_deriv_nonpos (convex_Ici 0)
      hc.continuousOn (fun s hs => (hd s (ne_of_gt (by simpa using hs))).differentiableAt.differentiableWithinAt)
      (fun s hs => hdle s (ne_of_gt (by simpa using hs)))
    have hb := mul_le_mul_of_nonneg_left (hm (by simp) ht ht) ht
    rw [hF0] at hb
    dsimp [F] at hb
    nlinarith [he]
  · have hm : AntitoneOn F (Iic 0) := antitoneOn_of_deriv_nonpos (convex_Iic 0)
      hc.continuousOn (fun s hs => (hd s (ne_of_lt (by simpa using hs))).differentiableAt.differentiableWithinAt)
      (fun s hs => hdle s (ne_of_lt (by simpa using hs)))
    have hb := mul_le_mul_of_nonpos_left (hm ht (by simp) ht) ht
    rw [hF0] at hb
    dsimp [F] at hb
    nlinarith [he]

/-- Exact `lem:ent-lsi`, with `n=m+1`: the exponent is
`L²t²/(2(m-1))`. Measurability and boundedness follow from the stated
geodesic Lipschitz condition and are not additional hypotheses. -/
theorem geodesic_lipschitz_centered_mgf
    (hLSI : BakryEmerySphereLogSobolev) {m : ℕ} (hm : 2 ≤ m)
    (g : Vector (m+1) → ℝ) {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L)
    (t : ℝ) :
    (∫ x, Real.exp (t * (g x - ∫ y, g y ∂unitSphereLaw (m+1)))
      ∂unitSphereLaw (m+1)) ≤ Real.exp (L ^ 2 * t ^ 2 / (2 * ((m : ℝ) - 1))) := by
  let μ := unitSphereLaw (m+1)
  obtain ⟨hgm, B, hB⟩ := geodesic_ae_bounded (by omega : 1 ≤ m+1) hg
  have hi (s : ℝ) : Integrable (fun x => Real.exp (s * g x)) μ :=
    bounded_exp_integrable μ g hgm hB s
  have hset : integrableExpSet g μ = univ := Set.eq_univ_of_forall hi
  have hd (s : ℝ) : HasDerivAt (mgf g μ) (∫ x, g x * Real.exp (s * g x) ∂μ) s :=
    hasDerivAt_mgf (by simp [hset])
  have hp (s : ℝ) : 0 < mgf g μ s := mgf_pos (hi s)
  have hlog (s : ℝ) : HasDerivAt (fun z => Real.log (mgf g μ z))
      ((∫ x, g x * Real.exp (s * g x) ∂μ) / mgf g μ s) s :=
    (hd s).log (hp s).ne'
  have hent (s : ℝ) : s * ((∫ x, g x * Real.exp (s * g x) ∂μ) / mgf g μ s) -
      Real.log (mgf g μ s) ≤ (L ^ 2 / (2 * ((m : ℝ) - 1))) * s ^ 2 := by
    have hh := hLSI (m+1) (by omega) g L hL hg s
    have he : (∫ x, Real.exp (s * g x) * (s * g x) ∂μ) =
        s * (∫ x, g x * Real.exp (s * g x) ∂μ) := by
      rw [← integral_const_mul]
      congr 1
      ext x
      ring
    change _ ≤ _ at hh
    rw [he] at hh
    have hdimen : (((m+1 : ℕ) : ℝ) - 2) = (m : ℝ) - 1 := by push_cast; ring
    rw [hdimen] at hh
    apply (le_of_mul_le_mul_right _ (hp s))
    change s * (∫ x, g x * Real.exp (s * g x) ∂μ) -
      mgf g μ s * Real.log (mgf g μ s) ≤ _ at hh
    convert hh using 1
    field_simp [(hp s).ne']
    ring
  have hb := herbst_of_log_mgf_differential (b := ∫ y, g y ∂μ) hlog (by simp [mgf])
    (by simp [mgf]) hent t
  have he : (∫ x, Real.exp (t * (g x - ∫ y, g y ∂μ)) ∂μ) =
      Real.exp (-t * ∫ y, g y ∂μ) * mgf g μ t := by
    unfold mgf
    rw [← integral_const_mul]
    congr 1
    ext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, ← Real.exp_log (hp t), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert (show -t * (∫ y, g y ∂μ) + Real.log (mgf g μ t) ≤
      (L ^ 2 / (2 * ((m : ℝ) - 1))) * t ^ 2 by linarith) using 1
  ring

private theorem unit_centered_mgf (hLSI : BakryEmerySphereLogSobolev)
    {n : ℕ} (hn : 3 ≤ n) (g : Vector n → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) (t : ℝ) :
    mgf (fun x => g x - ∫ y, g y ∂unitSphereLaw n) (unitSphereLaw n) t ≤
      Real.exp (L ^ 2 * t ^ 2 / (2 * ((n : ℝ) - 2))) := by
  cases n with
  | zero => omega
  | succ m =>
    have he : (((m+1 : ℕ) : ℝ) - 2) = (m : ℝ) - 1 := by push_cast; ring
    simpa only [mgf, Nat.succ_eq_add_one, he] using
      geodesic_lipschitz_centered_mgf hLSI (by omega) g hL hg t

private theorem unit_chord_le_geodesic {n : ℕ} (x y : Vector n)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x-y‖ ≤ Real.arccos (inner ℝ x y) := by
  have hi : |inner ℝ x y| ≤ 1 := by
    simpa only [hx, hy, mul_one] using abs_real_inner_le_norm x y
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.arccos (inner ℝ x y))
  rw [Real.cos_arccos (abs_le.mp hi).1 (abs_le.mp hi).2] at hc
  apply (sq_le_sq₀ (norm_nonneg _) (Real.arccos_nonneg _)).mp
  rw [norm_sub_sq_real, hx, hy]
  nlinarith

private theorem latitude_unit_scale_le {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : |r| ≤ 1) :
    Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)) * Real.sqrt (n : ℝ) ≤
      Real.sqrt ((n+1 : ℕ) : ℝ) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hq : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have ha : 0 ≤ (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)) := by positivity
  have hs := Real.sq_sqrt ha
  have hs' := Real.sq_sqrt hnpos.le
  have hsN := Real.sq_sqrt (Nat.cast_nonneg (n+1))
  have he : (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)) * Real.sqrt (n : ℝ)) ^ 2 =
      ((n+1 : ℕ) : ℝ)*(1-r^2) := by
    rw [mul_pow, hs, hs']
    field_simp
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [he, hsN]
  nlinarith [sq_nonneg r]

private theorem unit_latitudeLaw {n : ℕ} (hn : 1 ≤ n) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ) :
    (unitSphereLaw n).map (fun y => latitudeMap x e r (Real.sqrt (n : ℝ) • y)) =
      latitudeLaw x e r := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))).ne'
  have hT : Measurable (fun y : Vector n => latitudeMap x e r (Real.sqrt (n : ℝ) • y)) :=
    (latitudeMap_continuous x e r).measurable.comp (by fun_prop)
  rw [unitSphereLaw, Measure.map_map hT (by fun_prop), latitudeLaw]
  congr 1
  ext y
  simp [smul_smul, hs]

/-- The error-free MGF in `lem:ent-latitude` for the actual tangential
observable, before relaxing its precise curvature constant. The frozen
field and axis are arbitrary; their dependence on disorder is unrestricted. -/
theorem observable_centered_mgf_le_sharp
    (hLSI : BakryEmerySphereLogSobolev) {n P : ℕ} (hn : 3 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P) (hJ : J ∈ regularDisorder)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ} (hr : |r| ≤ 1) (t : ℝ) :
    mgf (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (latitudeLaw x e r) t ≤
      Real.exp (9 * (derivativeConstant c) ^ 2 * ((n+1 : ℕ) : ℝ) * t ^ 2 /
        (2 * ((n : ℝ) - 2))) := by
  let T : Vector n → Vector (n+1) := fun y => latitudeMap x e r (Real.sqrt (n : ℝ) • y)
  let F : Vector n → ℝ := fun y => observable c J x (T y)
  let L : ℝ := 3 * derivativeConstant c * Real.sqrt ((n+1 : ℕ) : ℝ)
  have hc : 0 ≤ derivativeConstant c := (derivativeConstant_pos c).le
  have hT : Measurable T := (latitudeMap_continuous x e r).measurable.comp (by fun_prop)
  have hF : Measurable F := (observable_continuous c J x).measurable.comp hT
  have hgeom : GeodesicLipschitz F L := by
    intro y z hy hz
    have hyn : ‖Real.sqrt (n : ℝ) • y‖ = Real.sqrt (n : ℝ) := by
      simp [norm_smul, hy, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hzn : ‖Real.sqrt (n : ℝ) • z‖ = Real.sqrt (n : ℝ) := by
      simp [norm_smul, hz, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hym := EntranceLatitudeConcentration.latitudeMap_mem_slice (by omega) x hx e he hr _ hyn
    have hzm := EntranceLatitudeConcentration.latitudeMap_mem_slice (by omega) x hx e he hr _ hzn
    have hLip := (observable_lipschitzOn (by omega) c J hJ x hx).dist_le_mul
      (T y) hym.1 (T z) hzm.1
    dsimp [T] at hLip
    rw [max_eq_left (show 0 ≤ 3 * derivativeConstant c by positivity), Real.dist_eq,
      EntranceLatitudeConcentration.latitudeMap_dist, dist_eq_norm, ← smul_sub,
      norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hLip
    change |F y-F z| ≤ _ at hLip
    calc
      _ ≤ (3 * derivativeConstant c) *
          (Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)) * Real.sqrt (n : ℝ)) * ‖y-z‖ := by
        convert hLip using 1
        ring
      _ ≤ L * ‖y-z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (latitude_unit_scale_le (by omega) hr) (by positivity)
      _ ≤ L * Real.arccos (inner ℝ y z) :=
        mul_le_mul_of_nonneg_left (unit_chord_le_geodesic y z hy hz) (by positivity)
  have hbound := unit_centered_mgf hLSI hn F (show 0 ≤ L by positivity) hgeom t
  have hlaw : (unitSphereLaw n).map T = latitudeLaw x e r :=
    unit_latitudeLaw (by omega) x e r
  have hmean : (∫ v, observable c J x v ∂latitudeLaw x e r) = ∫ y, F y ∂unitSphereLaw n := by
    rw [← hlaw, integral_map hT.aemeasurable (observable_continuous c J x).aestronglyMeasurable]
  have hmgf : mgf (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (latitudeLaw x e r) t =
      mgf (fun y => F y - ∫ z, F z ∂unitSphereLaw n) (unitSphereLaw n) t := by
    unfold mgf
    rw [hmean, ← hlaw]
    have hint : AEStronglyMeasurable
        (fun u => Real.exp (t * (observable c J x u - ∫ z, F z ∂unitSphereLaw n)))
        ((unitSphereLaw n).map T) :=
      (((observable_continuous c J x).sub continuous_const).const_mul t).rexp.aestronglyMeasurable
    change (∫ u, Real.exp (t * (observable c J x u - ∫ z, F z ∂unitSphereLaw n))
      ∂(unitSphereLaw n).map T) = _
    rw [integral_map hT.aemeasurable hint]
  rw [hmgf]
  have hsq : L ^ 2 = 9 * (derivativeConstant c) ^ 2 * ((n+1 : ℕ) : ℝ) := by
    dsimp [L]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  simpa only [hsq] using hbound

/-- A single constant fixed before dimension proves both clauses of
`lem:ent-latitude` on the already constructed original Gaussian-bank
event. The only analytic literature premise is the sphere LSI interface. -/
theorem center_latitude_mean_and_mgf (hLSI : BakryEmerySphereLogSobolev)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let C := 1 + |centerLatitudeMeanConstant μ Q| + 9 * (derivativeConstant c) ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn J hJ x hx r hr
  dsimp only
  constructor
  · have hh := actual_center_latitudeObservableMean_uniform_bound (by omega) μ hQ J hJ x hx hr
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [C]
    linarith [le_abs_self (centerLatitudeMeanConstant μ Q), sq_nonneg (derivativeConstant c)]
  · intro t
    have hh := observable_centered_mgf_le_sharp hLSI (by omega) c J hJ.1 x hx
      (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) (abs_lt.mpr hr).le t
    apply hh.trans
    apply Real.exp_le_exp.mpr
    have hnreal : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : 0 < 2 * ((n : ℝ)-2) := by linarith
    apply (div_le_iff₀ hden).mpr
    have hc : 0 ≤ 9 * (derivativeConstant c) ^ 2 * t ^ 2 := by positivity
    have hnscale : ((n+1 : ℕ) : ℝ) ≤ 2 * ((n : ℝ)-2) := by push_cast; linarith
    have hC : 9 * (derivativeConstant c) ^ 2 ≤ C := by
      dsimp [C]
      linarith [abs_nonneg (centerLatitudeMeanConstant μ Q)]
    calc
      _ = (9 * (derivativeConstant c) ^ 2 * t ^ 2) * ((n+1 : ℕ) : ℝ) := by ring
      _ ≤ (9 * (derivativeConstant c) ^ 2 * t ^ 2) * (2 * ((n : ℝ)-2)) :=
        mul_le_mul_of_nonneg_left hnscale hc
      _ ≤ (C * t ^ 2) * (2 * ((n : ℝ)-2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (sq_nonneg t)) hden.le

/-- The actual centered latitude observable satisfies Mathlib's genuine
sub-Gaussian predicate, including integrability of every exponential.
For `N=n+1≥6`, its variance proxy is `18 C₀²`, independent of dimension. -/
theorem observable_hasSubgaussianMGF (hLSI : BakryEmerySphereLogSobolev)
    {n P : ℕ} (hn : 5 ≤ n) (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (hJ : J ∈ regularDisorder) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ} (hr : |r| ≤ 1) :
    HasSubgaussianMGF
      (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (18 * (derivativeConstant c) ^ 2).toNNReal (latitudeLaw x e r) := by
  let lat := latitudeLaw x e r
  let V := observable c J x
  let B := derivativeConstant c * Real.sqrt ((n+1 : ℕ) : ℝ)
  have hV : AEStronglyMeasurable V lat := (observable_continuous c J x).aestronglyMeasurable
  have hb : ∀ᵐ u ∂lat, |V u| ≤ B := by
    filter_upwards [latitudeLaw_support (by omega) x hx e he hr] with u hu
    exact observable_abs_le (by omega) c J hJ x u hx hu.1
  have hm : |∫ v, V v ∂lat| ≤ B :=
    EntranceLatitudeGaussianRadius.integral_abs_le_bound lat V hV hb
  have hz : ∀ᵐ u ∂lat, |V u - ∫ v, V v ∂lat| ≤ 2 * B := by
    filter_upwards [hb] with u hu
    exact (abs_sub _ _).trans (by linarith)
  constructor
  · intro t
    exact bounded_exp_integrable lat _ (hV.sub aestronglyMeasurable_const) hz t
  · intro t
    have hh := observable_centered_mgf_le_sharp hLSI (by omega) c J hJ x hx e he hr t
    apply hh.trans
    apply Real.exp_le_exp.mpr
    rw [Real.coe_toNNReal _ (by positivity)]
    have hnreal : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : 0 < 2 * ((n : ℝ)-2) := by linarith
    apply (div_le_iff₀ hden).mpr
    have hnscale : ((n+1 : ℕ) : ℝ) ≤ 2 * ((n : ℝ)-2) := by push_cast; linarith
    have hh := mul_le_mul_of_nonneg_left hnscale
      (show 0 ≤ 9 * (derivativeConstant c) ^ 2 * t ^ 2 by positivity)
    convert hh using 1 <;> ring

private theorem exp_abs_le_exp_add (z t : ℝ) :
    Real.exp (t * |z|) ≤ Real.exp (t * z) + Real.exp (-t * z) := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-t*z)]
  · rw [abs_of_neg (lt_of_not_ge hz)]
    rw [show t * -z = -t * z by ring]
    linarith [Real.exp_pos (t*z)]

/-- The absolute exponential consequence used in the latitude moment
step of `prop:ent-multipliers`; both signs of the MGF are used. -/
theorem subgaussian_absolute_exponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * |Z x|)) μ ∧
      (∫ x, Real.exp (t * |Z x|) ∂μ) ≤ 2 * Real.exp ((c : ℝ) * t ^ 2 / 2) := by
  have hp := hZ.integrable_exp_mul t
  have hn := hZ.integrable_exp_mul (-t)
  have hmeas := hZ.aestronglyMeasurable
  have ha : Integrable (fun x => Real.exp (t * |Z x|)) μ := by
    apply (hp.add hn).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact exp_abs_le_exp_add _ _)
  refine ⟨ha, ?_⟩
  apply (integral_mono_ae ha (hp.add hn) (ae_of_all _ (fun x => exp_abs_le_exp_add _ _))).trans
  change (∫ x, Real.exp (t * Z x) + Real.exp (-t * Z x) ∂μ) ≤ _
  rw [integral_add hp hn]
  have hpos := hZ.mgf_le t
  have hneg := hZ.mgf_le (-t)
  simp only [neg_sq] at hneg
  unfold mgf at hpos hneg
  linarith

/-- Uniform fourth moment from the MGF, proved by the elementary fourth
Taylor term of the exponential rather than a separate tail premise. -/
theorem subgaussian_fourth_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) :
    Integrable (fun x => Z x ^ 4) μ ∧
      (∫ x, Z x ^ 4 ∂μ) ≤ 48 * Real.exp ((c : ℝ) / 2) := by
  have he (z : ℝ) : z ^ 4 ≤ 24 * Real.exp |z| := by
    have hh := Real.pow_div_factorial_le_exp |z| (abs_nonneg z) 4
    have habs : |z| ^ 4 = z ^ 4 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    norm_num [Nat.factorial, habs] at hh
    nlinarith
  have habs := subgaussian_absolute_exponential μ Z hZ 1
  have hi := habs.1.const_mul 24
  have hmeas := hZ.aestronglyMeasurable
  have hfour : Integrable (fun x => Z x ^ 4) μ := by
    apply hi.mono' (hmeas.pow 4)
    exact ae_of_all _ (fun x => by
      change ‖Z x ^ 4‖ ≤ 24 * Real.exp (1 * |Z x|)
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ Z x ^ 4), one_mul]
      exact he (Z x))
  refine ⟨hfour, ?_⟩
  apply (integral_mono_ae hfour hi (ae_of_all _ (fun x => by simpa using he (Z x)))).trans
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left habs.2 (by norm_num : (0 : ℝ) ≤ 24)
  simp only [one_pow, mul_one] at hh
  linarith

/-- The weighted second moment used in `prop:ent-multipliers`, with the
printed quadratic exponent and a dimension-independent prefactor. -/
theorem subgaussian_weighted_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) (t : ℝ) :
    Integrable (fun x => Z x ^ 2 * Real.exp (t * |Z x|)) μ ∧
      (∫ x, Z x ^ 2 * Real.exp (t * |Z x|) ∂μ) ≤
        4 * Real.exp (c : ℝ) * Real.exp ((c : ℝ) * t ^ 2) := by
  have he (z : ℝ) : z ^ 2 * Real.exp (t * |z|) ≤ 2 * Real.exp ((t+1) * |z|) := by
    have hh : z ^ 2 / 2 ≤ Real.exp |z| := by
      simpa only [sq_abs, Nat.factorial_two, Nat.cast_ofNat] using
        Real.pow_div_factorial_le_exp |z| (abs_nonneg z) 2
    have hm := mul_le_mul_of_nonneg_right (show z ^ 2 ≤ 2 * Real.exp |z| by linarith)
      (Real.exp_pos (t * |z|)).le
    apply hm.trans_eq
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have habs := subgaussian_absolute_exponential μ Z hZ (t+1)
  have hi := habs.1.const_mul 2
  have hmeas := hZ.aestronglyMeasurable
  have hsecond : Integrable (fun x => Z x ^ 2 * Real.exp (t * |Z x|)) μ := by
    apply hi.mono' (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact he _)
  refine ⟨hsecond, ?_⟩
  apply (integral_mono_ae hsecond hi (ae_of_all _ (fun x => he _))).trans
  rw [integral_const_mul]
  calc
    _ ≤ 4 * Real.exp ((c : ℝ) * (t+1) ^ 2 / 2) := by
      have hh := mul_le_mul_of_nonneg_left habs.2 (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    _ ≤ 4 * Real.exp ((c : ℝ) + (c : ℝ) * t ^ 2) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
      have hh := mul_nonneg c.coe_nonneg (sq_nonneg (t-1))
      nlinarith
    _ = _ := by rw [Real.exp_add]; ring

open SphericalForm SphericalGaussianJet ConditionedEntrance
open ConditionedEntrance.PhysicalHitting EntranceSmoothCutoffCalculus
open SphericalAging SphericalAging.HardSphereDynamics EntranceSmoothCutoffTensorApproximation

private theorem cutoff_deriv_zero (χ : ℝ → ℝ) {R t : ℝ}
    (hχ : ∀ s, R < |s| → χ s = 0) (ht : R < |t|) : deriv χ t = 0 := by
  have hO : IsOpen {s : ℝ | R < |s|} := isOpen_lt continuous_const continuous_abs
  have he : χ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    filter_upwards [hO.mem_nhds ht] with s hs
    exact hχ s hs
  exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he).deriv

private theorem regression_radial_small_overlap (μ : FiniteMixture)
    (Q n M R α r g X Y : ℝ)
    (hn : 0 ≤ n) (hM : 0 ≤ M) (hR : 0 ≤ R) (hα : 0 ≤ α)
    (hr : |r| ≤ 1) (hrα : |r| ≤ R*α) (hg : |g| ≤ n*(R*α))
    (hX : |X| ≤ M*n) (hY : |Y| ≤ M*n) :
    |valueThetaDerivative μ Q r*X+radialThetaDerivative μ Q r*Y-
      tangentThetaDerivative μ Q r*g| ≤
      regressionOrderConstant μ Q*(M+1)*n*(R*α)^(μ.minDegree-1) := by
  let C := regressionOrderConstant μ Q
  have hC : 0 ≤ C := (regressionOrderConstant_pos μ Q).le
  have hRa : 0 ≤ R*α := mul_nonneg hR hα
  have hp := mixed_regression_orders μ Q hr
  have hv0 : |valueThetaDerivative μ Q r|+|radialThetaDerivative μ Q r| ≤
      C*|r|^(μ.minDegree-1) := by
    have hv := hp.2.1
    change _ ≤ C*|r|^(μ.minDegree-1) at hv
    linarith [abs_nonneg (tangentTheta μ Q r)]
  have hv : |valueThetaDerivative μ Q r|+|radialThetaDerivative μ Q r| ≤
      C*(R*α)^(μ.minDegree-1) :=
    hv0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg r) hrα _) hC)
  have ht : |tangentThetaDerivative μ Q r| ≤ C*(R*α)^(μ.minDegree-2) :=
    hp.2.2.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg r) hrα _) hC)
  have he : (R*α)^(μ.minDegree-2)*(R*α)=(R*α)^(μ.minDegree-1) := by
    rw [←pow_succ, show μ.minDegree-2+1=μ.minDegree-1 by
      have := μ.minDegree_ge_two; omega]
  calc
    _ ≤ |valueThetaDerivative μ Q r*X+radialThetaDerivative μ Q r*Y| +
        |tangentThetaDerivative μ Q r*g| := by
      simpa only [sub_zero,zero_sub,abs_neg] using
        abs_sub_le (valueThetaDerivative μ Q r*X+radialThetaDerivative μ Q r*Y) 0
          (tangentThetaDerivative μ Q r*g)
    _ ≤ (|valueThetaDerivative μ Q r*X|+|radialThetaDerivative μ Q r*Y|)+
        |tangentThetaDerivative μ Q r*g| := add_le_add (abs_add_le _ _) le_rfl
    _ = |valueThetaDerivative μ Q r| * |X|+|radialThetaDerivative μ Q r| * |Y|+
        |tangentThetaDerivative μ Q r| * |g| := by rw [abs_mul,abs_mul,abs_mul]
    _ ≤ (|valueThetaDerivative μ Q r|+|radialThetaDerivative μ Q r|)*(M*n)+
        |tangentThetaDerivative μ Q r| * |g| := by
      rw [add_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hX (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hY (abs_nonneg _))) le_rfl
    _ ≤ (C*(R*α)^(μ.minDegree-1))*(M*n)+
        (C*(R*α)^(μ.minDegree-2))*(n*(R*α)) :=
      add_le_add (mul_le_mul_of_nonneg_right hv (mul_nonneg hM hn))
        (mul_le_mul ht hg (abs_nonneg _) (mul_nonneg hC (pow_nonneg hRa _)))
    _ = _ := by
      calc
        _=C*(M*n)*(R*α)^(μ.minDegree-1)+
          C*n*((R*α)^(μ.minDegree-2)*(R*α)) := by ring
        _=_ := by rw [he]; ring

private theorem regression_gradient_small_overlap {N : ℕ} (μ : FiniteMixture)
    (Q : ℝ) (u G : Vector N) (Hq Kq h k : ℝ) (x : Vector N)
    {M K R α : ℝ} (hN : 0 < (N : ℝ)) (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hα : 0 ≤ α) (hu : ‖u‖ = Real.sqrt (N : ℝ))
    (hG : ‖G‖ ≤ K*Real.sqrt (N : ℝ))
    (hr : |overlap x u| ≤ 1) (hrα : |overlap x u| ≤ R*α)
    (hg : |inner ℝ G x| ≤ (N : ℝ)*(R*α))
    (hX : |(N : ℝ)*h-Hq| ≤ M*(N : ℝ))
    (hY : |(N : ℝ)*k-Kq| ≤ M*(N : ℝ)) :
    ‖gradient (regressionCorrection μ Q u G Hq Kq h k) x‖ ≤
      regressionOrderConstant μ Q*(M+1+K)*Real.sqrt (N : ℝ)*
        (R*α)^(μ.minDegree-1) := by
  let C := regressionOrderConstant μ Q
  have hC : 0 ≤ C := (regressionOrderConstant_pos μ Q).le
  have hA := regression_radial_small_overlap μ Q (N : ℝ) M R α (overlap x u)
    (inner ℝ G x) ((N : ℝ)*h-Hq) ((N : ℝ)*k-Kq) hN.le hM hR hα hr hrα hg hX hY
  change |correctionRadialCoefficient μ Q u G Hq Kq h k x| ≤
    C*(M+1)*(N : ℝ)*(R*α)^(μ.minDegree-1) at hA
  have hdiv : |correctionRadialCoefficient μ Q u G Hq Kq h k x/(N : ℝ)| ≤
      C*(M+1)*(R*α)^(μ.minDegree-1) := by
    rw [abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    exact hA.trans_eq (by ring)
  have ht0 : |tangentTheta μ Q (overlap x u)| ≤
      C*|overlap x u|^(μ.minDegree-1) := by
    have hs := (mixed_regression_orders μ Q hr).2.1
    change _ ≤ C*|overlap x u|^(μ.minDegree-1) at hs
    linarith [abs_nonneg (valueThetaDerivative μ Q (overlap x u)),
      abs_nonneg (radialThetaDerivative μ Q (overlap x u))]
  have ht : |tangentTheta μ Q (overlap x u)| ≤ C*(R*α)^(μ.minDegree-1) :=
    ht0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) hrα _) hC)
  rw [(regressionCorrection_hasGradientAt μ Q u G Hq Kq h k x).gradient]
  calc
    _ ≤ ‖(correctionRadialCoefficient μ Q u G Hq Kq h k x/(N : ℝ)) • u‖+
        ‖tangentTheta μ Q (overlap x u) • G‖ := norm_sub_le _ _
    _ ≤ (C*(M+1)*(R*α)^(μ.minDegree-1))*Real.sqrt (N : ℝ)+
        (C*(R*α)^(μ.minDegree-1))*(K*Real.sqrt (N : ℝ)) := by
      simp only [norm_smul, Real.norm_eq_abs, hu]
      exact add_le_add (mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _))
        (mul_le_mul ht hG (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- The cutoff gradient constant depends on the fixed cutoff and the
mark bounds, and contains neither the scale nor the dimension. -/
def sourceCutoffGradientConstant (μ : FiniteMixture) (Q hbar kbar : ℝ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ :=
  let K := centerConstant μ Q
  let M := hbar+kbar+3*K
  (scalarCutoffConstant χ hχ 2)^2*regressionOrderConstant μ Q*
    ((M+1)*(1+K)*2^μ.minDegree+(M+1+K)*2^(μ.minDegree-1))

/-- The sharp `α^(d-1)` gradient clause of `eq:ent-cutoff-sup` for the
actual mixed source field. The former scale-dependent gradient premise
is discharged by the polynomial orders and both cutoff supports. -/
theorem regular_source_cutoff_gradient_uniform_scale {N : ℕ}
    (D : SmoothKilled.SourceData N) (hJ : D.disorder ∈ regularDisorder)
    (x : Vector N) (hx : OnSphere x) {hbar kbar : ℝ}
    (hh : |D.energyMark| ≤ hbar) (hk : |D.radialMark| ≤ kbar)
    (hχ0 : ∀ s, 2 < |s| → D.cutoff s = 0) :
    ‖gradient (fun y => D.hamiltonian y-fieldOfMixture D.mixture D.disorder y) x‖ ≤
      sourceCutoffGradientConstant D.mixture D.Q hbar kbar D.cutoff D.cutoff_smooth*
        Real.sqrt (N : ℝ)*D.cutoffScale^(D.mixture.minDegree-1) := by
  let c := centerCoefficients (mixtureCoefficients D.mixture) D.Q
  let G := surfaceGradient (field c D.disorder) D.axis
  let Hq := field c D.disorder D.axis
  let Kq := jet c 1 D.axis (fun _ => D.axis) D.disorder
  let F := regressionCorrection D.mixture D.Q D.axis G Hq Kq D.energyMark D.radialMark
  let a := D.cutoffScale
  let v1 := ((N : ℝ)*a)⁻¹ • D.axis
  let v2 := ((N : ℝ)*a)⁻¹ • G
  let C := regressionOrderConstant D.mixture D.Q
  let K := centerConstant D.mixture D.Q
  let M := hbar+kbar+3*K
  let L := scalarCutoffConstant D.cutoff D.cutoff_smooth 2
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by have := D.dimension_ge_one; omega)
  have ha : 0 < a := D.cutoffScale_pos
  have hK : 0 ≤ K := (centerConstant_pos _ _).le
  have hC : 0 ≤ C := (regressionOrderConstant_pos _ _).le
  have hhb : 0 ≤ hbar := (abs_nonneg _).trans hh
  have hkb : 0 ≤ kbar := (abs_nonneg _).trans hk
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hL : 0 ≤ L := scalarCutoffConstant_nonneg _ _ _
  have hUn := LandscapeDerivatives.sphere_norm D.axis
    ((onSphere_iff_norm_sq D.axis).mp D.axis_onSphere)
  obtain ⟨hH,hRad,hG⟩ := regular_center_observations D hJ
  change |Hq| ≤ K*(N : ℝ) at hH
  change |Kq| ≤ K*(N : ℝ) at hRad
  change ‖G‖ ≤ K*Real.sqrt (N : ℝ) at hG
  have hX : |(N : ℝ)*D.energyMark-Hq| ≤ M*(N : ℝ) := by
    have hs := abs_sub_le ((N : ℝ)*D.energyMark) 0 Hq
    simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos hNr] at hs
    have hm := mul_le_mul_of_nonneg_left hh hNr.le
    dsimp [M]
    nlinarith
  have hY : |(N : ℝ)*D.radialMark-Kq| ≤ M*(N : ℝ) := by
    have hs := abs_sub_le ((N : ℝ)*D.radialMark) 0 Kq
    simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_pos hNr] at hs
    have hm := mul_le_mul_of_nonneg_left hk hNr.le
    dsimp [M]
    nlinarith
  have hr : |overlap x D.axis| ≤ 1 := abs_le.mpr
    (overlap_mem_Icc_of_norm_sq D.dimension_ge_one x D.axis
      ((onSphere_iff_norm_sq x).mp hx) ((onSphere_iff_norm_sq D.axis).mp D.axis_onSphere))
  have he : (fun y => D.hamiltonian y-fieldOfMixture D.mixture D.disorder y) =
      cutoffCorrection D.cutoff D.cutoff v1 v2 F := by
    funext y
    change (fieldOfMixture D.mixture D.disorder y+
      cutoffCorrection D.cutoff D.cutoff v1 v2 F y)-
        fieldOfMixture D.mixture D.disorder y = _
    ring
  have hFd : DifferentiableAt ℝ F x :=
    ((regressionCorrection_contDiff D.dimension_ge_one D.mixture D.Q D.axis G Hq Kq
      D.energyMark D.radialMark).differentiable (by simp)) x
  have hχd := D.cutoff_smooth.differentiable (by norm_num)
  have hgrad := cutoffCorrection_gradient D.cutoff D.cutoff v1 v2 F x
    (hχd _) (hχd _) hFd
  have hconst : 0 ≤ sourceCutoffGradientConstant D.mixture D.Q hbar kbar
      D.cutoff D.cutoff_smooth := by
    change 0 ≤ L^2*C*((M+1)*(1+K)*2^D.mixture.minDegree+
      (M+1+K)*2^(D.mixture.minDegree-1))
    positivity
  rw [he]
  by_cases h1 : |inner ℝ v1 x| ≤ 2
  · by_cases h2 : |inner ℝ v2 x| ≤ 2
    · have harg1 : inner ℝ v1 x = overlap x D.axis/a := by
        dsimp [v1]
        rw [real_inner_smul_left, real_inner_comm]
        unfold overlap
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      have harg2 : inner ℝ v2 x = inner ℝ G x/((N : ℝ)*a) := by
        dsimp [v2]
        rw [real_inner_smul_left]
        exact (div_eq_inv_mul _ _).symm
      have hrα : |overlap x D.axis| ≤ 2*a := by
        rw [harg1, abs_div, abs_of_pos ha] at h1
        exact (div_le_iff₀ ha).mp h1
      have hgα : |inner ℝ G x| ≤ (N : ℝ)*(2*a) := by
        rw [harg2, abs_div, abs_of_pos (mul_pos hNr ha)] at h2
        have hs := (div_le_iff₀ (mul_pos hNr ha)).mp h2
        nlinarith
      obtain ⟨hb1,hd1⟩ := scalarCutoffConstant_bounds D.cutoff D.cutoff_smooth 2
        (inner ℝ v1 x) (abs_le.mp h1)
      obtain ⟨hb2,hd2⟩ := scalarCutoffConstant_bounds D.cutoff D.cutoff_smooth 2
        (inner ℝ v2 x) (abs_le.mp h2)
      have hval := regression_scalar_small_overlap D.mixture D.Q (N : ℝ) M 2 a
        (overlap x D.axis) (inner ℝ G x) ((N : ℝ)*D.energyMark-Hq)
          ((N : ℝ)*D.radialMark-Kq) hNr.le hM (by norm_num) ha.le hr hrα hgα hX hY
      change |F x| ≤ C*(M+1)*(N : ℝ)*(2*a)^D.mixture.minDegree at hval
      have hsmall := regression_gradient_small_overlap D.mixture D.Q D.axis G Hq Kq
        D.energyMark D.radialMark x hNr hM (by norm_num) ha.le hUn hG hr hrα hgα hX hY
      change ‖gradient F x‖ ≤ C*(M+1+K)*Real.sqrt (N : ℝ)*
        (2*a)^(D.mixture.minDegree-1) at hsmall
      have hv1 : ‖v1‖ = ((N : ℝ)*a)⁻¹*Real.sqrt (N : ℝ) := by
        simp only [v1, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le ha.le)), hUn]
      have hv2 : ‖v2‖ ≤ ((N : ℝ)*a)⁻¹*K*Real.sqrt (N : ℝ) := by
        simp only [v2, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le ha.le))]
        exact (mul_le_mul_of_nonneg_left hG (by positivity)).trans_eq (by ring)
      have hvs : ‖v1‖+‖v2‖ ≤ ((N : ℝ)*a)⁻¹*(1+K)*Real.sqrt (N : ℝ) :=
        (add_le_add hv1.le hv2).trans_eq (by ring)
      have hp := cutoffCorrection_gradient_norm_le D.cutoff hχd v1 v2 F x hFd
        hL hb1 hb2 hd1 hd2 hval hsmall
      apply hp.trans
      calc
        _ ≤ L^2*((C*(M+1)*(N : ℝ)*(2*a)^D.mixture.minDegree)*
            (((N : ℝ)*a)⁻¹*(1+K)*Real.sqrt (N : ℝ))+
              C*(M+1+K)*Real.sqrt (N : ℝ)*(2*a)^(D.mixture.minDegree-1)) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hvs (by positivity)) le_rfl) (sq_nonneg _)
        _ = _ := by
          change _ = (L^2*C*((M+1)*(1+K)*2^D.mixture.minDegree+
            (M+1+K)*2^(D.mixture.minDegree-1)))*Real.sqrt (N : ℝ)*a^(D.mixture.minDegree-1)
          have hap : a^D.mixture.minDegree = a^(D.mixture.minDegree-1)*a := by
            rw [←pow_succ, Nat.sub_add_cancel (D.mixture.minDegree_ge_two.trans' (by norm_num))]
          simp only [mul_pow, hap]
          field_simp [hNr.ne', ha.ne']
    · rw [hgrad, hχ0 _ (lt_of_not_ge h2), cutoff_deriv_zero D.cutoff hχ0 (lt_of_not_ge h2)]
      simp only [mul_zero, zero_mul, zero_smul, add_zero, norm_zero]
      positivity
  · rw [hgrad, hχ0 _ (lt_of_not_ge h1), cutoff_deriv_zero D.cutoff hχ0 (lt_of_not_ge h1)]
    simp only [zero_mul, zero_smul, zero_add, norm_zero]
    positivity

/-- One dimension- and scale-independent constant for both deterministic
supremum clauses of `prop:ent-multipliers`. -/
def sourceCutoffSupremumConstant (μ : FiniteMixture) (Q hbar kbar : ℝ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ :=
  1+uniformCutoffEnergyConstant μ Q hbar kbar 1 2+
    sourceCutoffGradientConstant μ Q hbar kbar χ hχ

/-- Both sharp source cutoff bounds with one constant. The hypotheses
are actual regular disorder, bounded marks, and the fixed smooth cutoff;
the gradient bound is now proved rather than a scale-dependent input. -/
theorem regular_source_cutoff_value_and_gradient {N : ℕ}
    (D : SmoothKilled.SourceData N) (hJ : D.disorder ∈ regularDisorder)
    (x : Vector N) (hx : OnSphere x) {hbar kbar : ℝ}
    (hh : |D.energyMark| ≤ hbar) (hk : |D.radialMark| ≤ kbar)
    (hχb : ∀ s, |D.cutoff s| ≤ 1) (hχ0 : ∀ s, 2 < |s| → D.cutoff s = 0) :
    let C := sourceCutoffSupremumConstant D.mixture D.Q hbar kbar D.cutoff D.cutoff_smooth
    0 < C ∧
      |D.hamiltonian x-fieldOfMixture D.mixture D.disorder x| ≤
        C*(N : ℝ)*D.cutoffScale^D.mixture.minDegree ∧
      ‖gradient (fun y => D.hamiltonian y-fieldOfMixture D.mixture D.disorder y) x‖ ≤
        C*Real.sqrt (N : ℝ)*D.cutoffScale^(D.mixture.minDegree-1) := by
  have hhb : 0 ≤ hbar := (abs_nonneg _).trans hh
  have hkb : 0 ≤ kbar := (abs_nonneg _).trans hk
  have hK := (centerConstant_pos D.mixture D.Q).le
  have hM : 0 ≤ hbar+kbar+3*centerConstant D.mixture D.Q := by positivity
  have hE : 0 ≤ uniformCutoffEnergyConstant D.mixture D.Q hbar kbar 1 2 := by
    unfold uniformCutoffEnergyConstant
    exact cutoffEnergyConstant_nonneg _ _ _ _ _ hM (by norm_num)
  have hG : 0 ≤ sourceCutoffGradientConstant D.mixture D.Q hbar kbar
      D.cutoff D.cutoff_smooth := by
    unfold sourceCutoffGradientConstant
    have hL := scalarCutoffConstant_nonneg D.cutoff D.cutoff_smooth 2
    have hC := (regressionOrderConstant_pos D.mixture D.Q).le
    positivity
  dsimp only
  refine ⟨by unfold sourceCutoffSupremumConstant; positivity, ?_, ?_⟩
  · have hv := regular_source_cutoff_energy_difference_uniform_marks D hJ x hx hh hk
      (by norm_num) (by norm_num) hχb hχ0
    apply hv.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg D.cutoffScale_pos.le _)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
    unfold sourceCutoffSupremumConstant
    linarith
  · have hg := regular_source_cutoff_gradient_uniform_scale D hJ x hx hh hk hχ0
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg D.cutoffScale_pos.le _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    unfold sourceCutoffSupremumConstant
    linarith

/-- All four mixed-model conclusions of `prop:ent-multipliers` with a
common constant and cutoff scale selected before dimension. This uses
the actual original-bank good event; the manuscript harmonic-event
identification remains separate. The proper-pure case is proved below. -/
theorem mixed_source_cutoff_multipliers_and_suprema (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree) {Q M β : ℝ} (hQ : 0 < Q) (hQone : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχ0 : ∀ s, 2 < |s| → χ s = 0) :
    ∃ α₀ C : ℝ, ∃ N₀ : ℕ,
      0 < α₀ ∧ α₀ ≤ 1/8 ∧ 0 < C ∧
      ∀ (n : ℕ), N₀ ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ originalLatitudeMeanGood n μ →
      ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∀ e k : ℝ, |e| ≤ M → |k| ≤ M →
      ∀ (x : Vector (n+1)), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      let W := fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-
        fieldOfMixture μ J x
      (∫ u, |Real.exp (β*W u)-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u, Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) ∧
      ∀ (u : Vector (n+1)), OnSphere u →
        |W u| ≤ C*((n+1 : ℕ) : ℝ)*α^μ.minDegree ∧
        ‖gradient (fun y => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ y-
            fieldOfMixture μ J y) x‖ ≤
          C*Real.sqrt ((n+1 : ℕ) : ℝ)*α^(μ.minDegree-1) := by
  obtain ⟨Cmom,hCmom,hMom⟩ := actual_sourceSmoothCutoffField_tilt_moments μ hd
    hQ hnp hM hβ
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hMom
  let α₀ := min (1/8 : ℝ) (sourceCutoffMomentScale μ Q M (2*β))
  let Cs := sourceCutoffSupremumConstant μ Q M M χ hχ
  let C := 1+Cmom+Cs
  have hK := (centerConstant_pos μ Q).le
  have hmark : 0 ≤ M+M+3*centerConstant μ Q := by positivity
  have hE : 0 ≤ uniformCutoffEnergyConstant μ Q M M 1 2 := by
    unfold uniformCutoffEnergyConstant
    exact cutoffEnergyConstant_nonneg _ _ _ _ _ hmark (by norm_num)
  have hG : 0 ≤ sourceCutoffGradientConstant μ Q M M χ hχ := by
    unfold sourceCutoffGradientConstant
    have hL := scalarCutoffConstant_nonneg χ hχ 2
    have hC := (regressionOrderConstant_pos μ Q).le
    positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs,sourceCutoffSupremumConstant]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hα₀ : 0 < α₀ := lt_min (by norm_num) (sourceCutoffMomentScale_pos μ Q M (2*β))
  refine ⟨α₀,C,N₀,hα₀,min_le_left _ _,hC,?_⟩
  intro n hn J hJ α hα hαsmall e k he hk x hx
  dsimp only
  have hαscale : α ≤ sourceCutoffMomentScale μ Q M (2*β) :=
    hαsmall.trans (min_le_right _ _)
  obtain ⟨heta,heps⟩ := hN₀ n hn J hJ x hx α hα hαscale χ hχ hχb hχ0 e k he hk
  have hCm : Cmom ≤ C := by dsimp [C]; linarith
  have hCsc : Cs ≤ C := by dsimp [C]; linarith
  refine ⟨heta.trans (mul_le_mul_of_nonneg_right hCm (by positivity)),
    heps.trans (mul_le_mul_of_nonneg_right hCm (by positivity)),?_⟩
  intro u hu
  let D : SmoothKilled.SourceData (n+1) := {
    dimension_ge_one := by omega
    mixture := μ
    nonpure := hnp
    Q := Q
    Q_pos := hQ
    Q_le_one := hQone
    disorder := J
    axis := u
    axis_onSphere := hu
    energyMark := e
    radialMark := k
    cutoffScale := α
    cutoffScale_pos := hα
    cutoff := χ
    cutoff_smooth := hχ }
  have hxS : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  obtain ⟨_,hval,hgrad⟩ := regular_source_cutoff_value_and_gradient D hJ.1 x hxS he hk hχb hχ0
  change |sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-fieldOfMixture μ J x| ≤
    Cs*((n+1 : ℕ) : ℝ)*α^μ.minDegree at hval
  change ‖gradient (fun y => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ y-
      fieldOfMixture μ J y) x‖ ≤ Cs*Real.sqrt ((n+1 : ℕ) : ℝ)*α^(μ.minDegree-1) at hgrad
  constructor
  · exact hval.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCsc (Nat.cast_nonneg _)) (pow_nonneg hα.le _))
  · exact hgrad.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCsc (Real.sqrt_nonneg _)) (pow_nonneg hα.le _))

private theorem homogeneous_two_term_bound (j : ℕ) (hj : 1 ≤ j)
    (A M n z a b X g : ℝ) (hA : 0 ≤ A)
    (hz : 0 ≤ z) (ha : |a| ≤ A*z^j) (hb : |b| ≤ A*z^(j-1))
    (hX : |X| ≤ M*n) (hg : |g| ≤ n*z) :
    |a*X-b*g| ≤ A*(M+1)*n*z^j := by
  have he : z^(j-1)*z = z^j := by rw [← pow_succ, Nat.sub_add_cancel hj]
  calc
    _ ≤ |a*X|+|b*g| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (a*X) 0 (b*g)
    _ ≤ (A*z^j)*(M*n)+(A*z^(j-1))*(n*z) := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul ha hX (abs_nonneg _) (by positivity))
        (mul_le_mul hb hg (abs_nonneg _) (by positivity))
    _ = _ := by
      calc
        _ = A*(M*n)*z^j+A*n*(z^(j-1)*z) := by ring
        _ = _ := by rw [he]; ring

private theorem pure_regression_small_overlap {N : ℕ} (p : ℕ) (hp : 2 ≤ p)
    (Q : ℝ) (u G x : Vector N) (Hq e : ℝ) {M K z : ℝ}
    (hN : 0 < (N : ℝ)) (hz : 0 ≤ z)
    (hu : ‖u‖ = Real.sqrt (N : ℝ)) (hG : ‖G‖ ≤ K*Real.sqrt (N : ℝ))
    (hr : |overlap x u| ≤ z) (hg : |inner ℝ G x| ≤ (N : ℝ)*z)
    (hX : |(N : ℝ)*e-Hq| ≤ M*(N : ℝ)) :
    |pureRegressionCorrection p Q u G Hq e x| ≤
      pureOrderConstant Q p*(M+1)*(N : ℝ)*z^p ∧
    ‖gradient (pureRegressionCorrection p Q u G Hq e) x‖ ≤
      pureOrderConstant Q p*(M+1+K)*Real.sqrt (N : ℝ)*z^(p-1) := by
  let A := pureOrderConstant Q p
  let r := overlap x u
  have hA : 0 ≤ A := (pureOrderConstant_pos Q p).le
  obtain ⟨hv0,hpair,htd0⟩ := pure_regression_orders Q p r
  have hv : |pureValueTheta Q p r| ≤ A*z^p :=
    hv0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hr _) hA)
  have ht0 : |pureTangentTheta Q p r| ≤ A*|r|^(p-1) := by
    change _ ≤ A*|r|^(p-1) at hpair
    linarith [abs_nonneg (purePrefactor Q p*(p : ℝ)*r^(p-1))]
  have ht : |pureTangentTheta Q p r| ≤ A*z^(p-1) :=
    ht0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hr _) hA)
  have hvd0 : |purePrefactor Q p*(p : ℝ)*r^(p-1)| ≤ A*|r|^(p-1) := by
    change _ ≤ A*|r|^(p-1) at hpair
    linarith [abs_nonneg (pureTangentTheta Q p r)]
  have hvd : |purePrefactor Q p*(p : ℝ)*r^(p-1)| ≤ A*z^(p-1) :=
    hvd0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hr _) hA)
  have htd : |purePrefactor Q p*((p-1 : ℕ) : ℝ)*r^(p-2)| ≤ A*z^(p-2) :=
    htd0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hr _) hA)
  have hval := homogeneous_two_term_bound p (by omega) A M (N : ℝ) z
    (pureValueTheta Q p r) (pureTangentTheta Q p r)
    ((N : ℝ)*e-Hq) (inner ℝ G x) hA hz hv ht hX hg
  have hrad := homogeneous_two_term_bound (p-1) (by omega) A M (N : ℝ) z
    (purePrefactor Q p*(p : ℝ)*r^(p-1))
    (purePrefactor Q p*((p-1 : ℕ) : ℝ)*r^(p-2))
    ((N : ℝ)*e-Hq) (inner ℝ G x) hA hz hvd
    (by simpa only [show p-1-1=p-2 by omega] using htd) hX hg
  constructor
  · convert hval using 1
    unfold pureRegressionCorrection pureValueTheta pureTangentTheta purePrefactor r
    congr 1
    ring
  · rw [(pureRegressionCorrection_hasGradientAt p Q u G Hq e x).gradient]
    have hdiv :
        |(purePrefactor Q p*(p : ℝ)*r^(p-1)*((N : ℝ)*e-Hq)-
          purePrefactor Q p*((p-1 : ℕ) : ℝ)*r^(p-2)*inner ℝ G x)/(N : ℝ)| ≤
            A*(M+1)*z^(p-1) := by
      rw [abs_div,abs_of_pos hN]
      apply (div_le_iff₀ hN).mpr
      exact hrad.trans_eq (by ring)
    calc
      _ ≤ ‖((purePrefactor Q p*(p : ℝ)*(overlap x u)^(p-1)*((N : ℝ)*e-Hq)-
          purePrefactor Q p*((p-1 : ℕ) : ℝ)*(overlap x u)^(p-2)*inner ℝ G x)/(N : ℝ)) • u‖+
          ‖pureTangentTheta Q p (overlap x u) • G‖ := norm_sub_le _ _
      _ ≤ (A*(M+1)*z^(p-1))*Real.sqrt (N : ℝ)+
          (A*z^(p-1))*(K*Real.sqrt (N : ℝ)) := by
        simp only [norm_smul,Real.norm_eq_abs,hu]
        exact add_le_add (mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _))
          (mul_le_mul ht hG (norm_nonneg _) (by positivity))
      _ = _ := by ring

/-- The proper-pure cutoff gradient constant is fixed before the
dimension and cutoff scale. The singular radial score is not inverted. -/
def pureSourceCutoffGradientConstant (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q B : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ :=
  let K := centerConstant (FiniteMixture.pure p hp c hc) Q
  let M := B+K
  (scalarCutoffConstant χ hχ 2)^2*pureOrderConstant Q p*
    ((M+1)*(1+K)*2^p+(M+1+K)*2^(p-1))

/-- The proper-pure sharp gradient clause of `eq:ent-cutoff-sup`,
proved on the actual original tensor regularity event for every scale. -/
theorem regular_pure_source_cutoff_gradient_uniform_scale (n p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) {Q B α : ℝ} (hB : 0 ≤ B) (hα : 0 < α)
    (J : Disorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (u x : Vector (n+1)) (hu : OnSphere u)
    (e : ℝ) (he : |e| ≤ B) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχ0 : ∀ s, 2 < |s| → χ s = 0) :
    let μ := FiniteMixture.pure p hp c hc
    ‖gradient (fun y => pureSourceSmoothCutoffField p hp c hc Q J u e α χ y-
      fieldOfMixture μ J y) x‖ ≤
      pureSourceCutoffGradientConstant p hp c hc Q B χ hχ*
        Real.sqrt ((n+1 : ℕ) : ℝ)*α^(p-1) := by
  dsimp only
  let μ := FiniteMixture.pure p hp c hc
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let G := surfaceGradient (field cQ J) u
  let Hq := field cQ J u
  let F := pureRegressionCorrection p Q u G Hq e
  let v1 := (((n+1 : ℕ) : ℝ)*α)⁻¹ • u
  let v2 := (((n+1 : ℕ) : ℝ)*α)⁻¹ • G
  let A := pureOrderConstant Q p
  let K := centerConstant μ Q
  let M := B+K
  let L := scalarCutoffConstant χ hχ 2
  have hNr : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hA : 0 ≤ A := (pureOrderConstant_pos Q p).le
  have hK : 0 ≤ K := (centerConstant_pos μ Q).le
  have hM : 0 ≤ M := add_nonneg hB hK
  have hL : 0 ≤ L := scalarCutoffConstant_nonneg χ hχ 2
  have hun := LandscapeDerivatives.sphere_norm u ((onSphere_iff_norm_sq u).mp hu)
  obtain ⟨hH,hG⟩ := regular_pure_center_observations (by omega) p hp c hc Q J hJ u hu
  change |Hq| ≤ K*((n+1 : ℕ) : ℝ) at hH
  change ‖G‖ ≤ K*Real.sqrt ((n+1 : ℕ) : ℝ) at hG
  have hX : |((n+1 : ℕ) : ℝ)*e-Hq| ≤ M*((n+1 : ℕ) : ℝ) := by
    have hs := abs_sub_le (((n+1 : ℕ) : ℝ)*e) 0 Hq
    simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_pos hNr] at hs
    have hm := mul_le_mul_of_nonneg_left he hNr.le
    dsimp [M]
    nlinarith
  have harg1 (y : Vector (n+1)) : inner ℝ v1 y = overlap y u/α := by
    dsimp [v1]
    rw [real_inner_smul_left,real_inner_comm]
    unfold overlap
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have harg2 (y : Vector (n+1)) : inner ℝ v2 y = inner ℝ G y/(((n+1 : ℕ) : ℝ)*α) := by
    dsimp [v2]
    rw [real_inner_smul_left]
    exact (div_eq_inv_mul _ _).symm
  have hfun : (fun y => pureSourceSmoothCutoffField p hp c hc Q J u e α χ y-
      fieldOfMixture μ J y) = cutoffCorrection χ χ v1 v2 F := by
    funext y
    change (fieldOfMixture μ J y+χ (overlap y u/α)*
      χ (inner ℝ G y/(((n+1 : ℕ) : ℝ)*α))*F y)-fieldOfMixture μ J y =
      χ (inner ℝ v1 y)*χ (inner ℝ v2 y)*F y
    rw [harg1,harg2]
    ring
  have hFd : DifferentiableAt ℝ F x :=
    (pureRegressionCorrection_hasGradientAt p Q u G Hq e x).differentiableAt
  have hχd := hχ.differentiable (by norm_num)
  have hgrad := cutoffCorrection_gradient χ χ v1 v2 F x (hχd _) (hχd _) hFd
  have hconst : 0 ≤ pureSourceCutoffGradientConstant p hp c hc Q B χ hχ := by
    change 0 ≤ L^2*A*((M+1)*(1+K)*2^p+(M+1+K)*2^(p-1))
    positivity
  rw [hfun]
  by_cases h1 : |inner ℝ v1 x| ≤ 2
  · by_cases h2 : |inner ℝ v2 x| ≤ 2
    · have hrα : |overlap x u| ≤ 2*α := by
        rw [harg1,abs_div,abs_of_pos hα] at h1
        exact (div_le_iff₀ hα).mp h1
      have hgα : |inner ℝ G x| ≤ ((n+1 : ℕ) : ℝ)*(2*α) := by
        rw [harg2,abs_div,abs_of_pos (mul_pos hNr hα)] at h2
        have hs := (div_le_iff₀ (mul_pos hNr hα)).mp h2
        nlinarith
      obtain ⟨hb1,hd1⟩ := scalarCutoffConstant_bounds χ hχ 2 (inner ℝ v1 x) (abs_le.mp h1)
      obtain ⟨hb2,hd2⟩ := scalarCutoffConstant_bounds χ hχ 2 (inner ℝ v2 x) (abs_le.mp h2)
      obtain ⟨hval,hsmall⟩ := pure_regression_small_overlap p hp Q u G x Hq e
        hNr (show 0 ≤ 2*α by positivity) hun hG hrα hgα hX
      change |F x| ≤ A*(M+1)*((n+1 : ℕ) : ℝ)*(2*α)^p at hval
      change ‖gradient F x‖ ≤ A*(M+1+K)*Real.sqrt ((n+1 : ℕ) : ℝ)*(2*α)^(p-1) at hsmall
      have hv1 : ‖v1‖ = (((n+1 : ℕ) : ℝ)*α)⁻¹*Real.sqrt ((n+1 : ℕ) : ℝ) := by
        simp only [v1,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le hα.le)),hun]
      have hv2 : ‖v2‖ ≤ (((n+1 : ℕ) : ℝ)*α)⁻¹*K*Real.sqrt ((n+1 : ℕ) : ℝ) := by
        simp only [v2,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le hα.le))]
        exact (mul_le_mul_of_nonneg_left hG (by positivity)).trans_eq (by ring)
      have hvs : ‖v1‖+‖v2‖ ≤ (((n+1 : ℕ) : ℝ)*α)⁻¹*(1+K)*Real.sqrt ((n+1 : ℕ) : ℝ) :=
        (add_le_add hv1.le hv2).trans_eq (by ring)
      have hh := cutoffCorrection_gradient_norm_le χ hχd v1 v2 F x hFd hL hb1 hb2 hd1 hd2 hval hsmall
      apply hh.trans
      calc
        _ ≤ L^2*((A*(M+1)*((n+1 : ℕ) : ℝ)*(2*α)^p)*
            ((((n+1 : ℕ) : ℝ)*α)⁻¹*(1+K)*Real.sqrt ((n+1 : ℕ) : ℝ))+
            A*(M+1+K)*Real.sqrt ((n+1 : ℕ) : ℝ)*(2*α)^(p-1)) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hvs (by positivity)) le_rfl) (sq_nonneg _)
        _ = _ := by
          change _ = (L^2*A*((M+1)*(1+K)*2^p+(M+1+K)*2^(p-1)))*
            Real.sqrt ((n+1 : ℕ) : ℝ)*α^(p-1)
          have hap : α^p = α^(p-1)*α := by rw [←pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ p)]
          simp only [mul_pow,hap]
          field_simp [hNr.ne',hα.ne']
    · rw [hgrad,hχ0 _ (lt_of_not_ge h2),cutoff_deriv_zero χ hχ0 (lt_of_not_ge h2)]
      simp only [mul_zero,zero_mul,zero_smul,add_zero,norm_zero]
      positivity
  · rw [hgrad,hχ0 _ (lt_of_not_ge h1),cutoff_deriv_zero χ hχ0 (lt_of_not_ge h1)]
    simp only [zero_mul,zero_smul,zero_add,norm_zero]
    positivity

/-- A common fixed constant for proper-pure cutoff values and gradients. -/
def pureSourceCutoffSupremumConstant (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    (Q B : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ :=
  1+purePrefactor Q p*(B+centerConstant (FiniteMixture.pure p hp c hc) Q+1)*2^p+
    pureSourceCutoffGradientConstant p hp c hc Q B χ hχ

/-- Both averaged multiplier rates and both sharp deterministic cutoff
bounds for every proper-pure amplitude, with common constants fixed before
the dimension and scale, on the actual original Gaussian-bank event. -/
theorem pure_source_cutoff_multipliers_and_suprema (p : ℕ) (hp : 4 ≤ p)
    (c : ℝ) (hc : 0 < c) {Q M β : ℝ} (hQ : 0 < Q) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχ0 : ∀ s, 2 < |s| → χ s = 0) :
    let μ := FiniteMixture.pure p (by omega) c hc
    ∃ α₀ C : ℝ, ∃ N₀ : ℕ,
      0 < α₀ ∧ α₀ ≤ 1/8 ∧ 0 < C ∧
      ∀ (n : ℕ), N₀ ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ originalLatitudeMeanGood n μ →
      ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∀ e : ℝ, |e| ≤ M →
      ∀ (x : Vector (n+1)), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      let W := fun u => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x-
        fieldOfMixture μ J x
      (∫ u, |Real.exp (β*W u)-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u, Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) ∧
      ∀ (u : Vector (n+1)), OnSphere u →
        |W u| ≤ C*((n+1 : ℕ) : ℝ)*α^p ∧
        ‖gradient (fun y => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ y-
            fieldOfMixture μ J y) x‖ ≤
          C*Real.sqrt ((n+1 : ℕ) : ℝ)*α^(p-1) := by
  let hp2 : 2 ≤ p := by omega
  let μ := FiniteMixture.pure p hp2 c hc
  obtain ⟨Cmom,hCmom,hMom⟩ := actual_pureSourceSmoothCutoffField_tilt_moments p hp c hc hQ hM hβ
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hMom
  let α₀ := min (1/8 : ℝ) (sourceCutoffMomentScale μ Q M (2*β))
  let Cs := pureSourceCutoffSupremumConstant p hp2 c hc Q M χ hχ
  let C := 1+Cmom+Cs
  have hK := (centerConstant_pos μ Q).le
  have hE : 0 ≤ purePrefactor Q p*(M+centerConstant μ Q+1)*2^p := by
    unfold purePrefactor
    positivity
  have hG : 0 ≤ pureSourceCutoffGradientConstant p hp2 c hc Q M χ hχ := by
    unfold pureSourceCutoffGradientConstant
    have hL := scalarCutoffConstant_nonneg χ hχ 2
    have hA := (pureOrderConstant_pos Q p).le
    positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs,pureSourceCutoffSupremumConstant]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hα₀ : 0 < α₀ := lt_min (by norm_num) (sourceCutoffMomentScale_pos μ Q M (2*β))
  refine ⟨α₀,C,N₀,hα₀,min_le_left _ _,hC,?_⟩
  intro n hn J hJ α hα hαsmall e he x hx
  dsimp only
  have hαscale : α ≤ sourceCutoffMomentScale μ Q M (2*β) := hαsmall.trans (min_le_right _ _)
  obtain ⟨heta,heps⟩ := hN₀ n hn J hJ x hx α hα hαscale χ hχ hχb hχ0 e he
  have hCm : Cmom ≤ C := by dsimp [C]; linarith
  have hCsc : Cs ≤ C := by dsimp [C]; linarith
  refine ⟨heta.trans (mul_le_mul_of_nonneg_right hCm (by positivity)),
    heps.trans (mul_le_mul_of_nonneg_right hCm (by positivity)),?_⟩
  intro u hu
  have hxS : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  have hval := regular_pure_source_cutoff_energy_difference n p hp2 c hc hQ hM hα J hJ.1 u x hu hxS e he χ hχb hχ0
  have hgrad := regular_pure_source_cutoff_gradient_uniform_scale n p hp2 c hc (Q := Q) hM hα J hJ.1 u x hu e he χ hχ hχ0
  have hCe : purePrefactor Q p*(M+centerConstant μ Q+1)*2^p ≤ C := by
    dsimp [C,Cs,pureSourceCutoffSupremumConstant]
    linarith
  have hCg : pureSourceCutoffGradientConstant p hp2 c hc Q M χ hχ ≤ C := by
    dsimp [C,Cs,pureSourceCutoffSupremumConstant]
    linarith
  constructor
  · apply hval.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCe (Nat.cast_nonneg _)) (pow_nonneg hα.le _)
  · exact hgrad.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCg (Real.sqrt_nonneg _)) (pow_nonneg hα.le _))

end SlowEquilibration.SourceSphereSharpConcentration
