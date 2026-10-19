-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceSphereLogSobolevFinal

/-! Gaussian projection and the origin approximation for Section 8,
`lem:ent-lsi` and `lem:ent-latitude`.

The angular lift is approximated by uniformly bounded globally Lipschitz
functions, agreeing with it outside shrinking balls. Both exponential
entropy and the actual integrated derivative energy converge. Consequently
the exact sphere interface follows from Gross's integrated-gradient
inequality just for bounded globally Lipschitz Gaussian observables.

The latter Gaussian inequality remains an explicit premise of the reduction
theorems below; this module does not claim to have proved Gross's theorem.
In particular, almost-everywhere differentiability alone is never used as
a substitute for Lipschitz or Sobolev regularity.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceSphereLogSobolevProof

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceSphereSharpConcentration SourceSphereLogSobolev
open SourceSphereLogSobolevFinal
open SphericalGaussianJet EntranceLatitudeTangentObservable
open scoped Topology RealInnerProductSpace NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Exponential entropy, with the actual standard Gaussian normalization. -/
def gaussianEntropy {n : ℕ} (f : Vector n → ℝ) : ℝ :=
  (∫ x, Real.exp (f x) * f x ∂stdGaussian (Vector n)) -
    (∫ x, Real.exp (f x) ∂stdGaussian (Vector n)) *
      Real.log (∫ x, Real.exp (f x) ∂stdGaussian (Vector n))

/-- Integrated exponential Dirichlet energy, rather than a uniform
Lipschitz bound substituted after integration. -/
def gaussianEnergy {n : ℕ} (f : Vector n → ℝ) : ℝ :=
  ∫ x, Real.exp (f x) * ‖fderiv ℝ f x‖ ^ 2 ∂stdGaussian (Vector n)

/-- The remaining Gross inequality on a regular class. The approximation
theorem below removes the singular origin of angular lifts from its scope. -/
def BoundedLipschitzGaussianLogSobolev : Prop :=
  ∀ (n : ℕ) (f : Vector n → ℝ) (K : ℝ≥0), LipschitzWith K f →
    (∃ B : ℝ, ∀ x, |f x| ≤ B) →
      gaussianEntropy f ≤ (1 / 2 : ℝ) * gaussianEnergy f

private theorem angularLift_bounded {n : ℕ} {g : Vector n → ℝ} {L : ℝ}
    (hg : GeodesicLipschitz g L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |angularLift g x| ≤ B := by
  have hc : ContinuousOn g {x | ‖x‖ = 1} := by
    intro x hx
    have hxn : ‖x‖ = 1 := hx
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hh : Tendsto (fun y : Vector n => L * Real.arccos (inner ℝ y x))
        (𝓝[{x | ‖x‖ = 1}] x) (𝓝 0) := by
      have hcont : Continuous (fun y : Vector n => L * Real.arccos (inner ℝ y x)) := by
        fun_prop
      simpa [real_inner_self_eq_norm_sq, hxn] using
        (hcont.continuousAt (x := x)).tendsto.mono_left nhdsWithin_le_nhds
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hh
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa only [Real.norm_eq_abs] using hg y x hy hx
  have hs : {x : Vector n | ‖x‖ = 1} = Metric.sphere 0 1 := by
    ext x
    simp
  obtain ⟨C, hC⟩ := (show IsCompact {x : Vector n | ‖x‖ = 1} by
    rw [hs]
    exact isCompact_sphere 0 1).exists_bound_of_continuousOn hc
  refine ⟨max C |g 0|, (abs_nonneg (g 0)).trans (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simpa only [angularLift, norm_zero, inv_zero, zero_smul] using
      (le_max_right C |g 0|)
  · have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
      simpa only [NormedSpace.normalize] using NormedSpace.norm_normalize hx
    have hb : |g (‖x‖⁻¹ • x)| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (‖x‖⁻¹ • x) hu
    exact hb.trans (le_max_left _ _)

private theorem exists_bounded_lipschitz_extension
    {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {s : Set E}
    {K : ℝ≥0} {B : ℝ} (hB : 0 ≤ B)
    (hf : LipschitzOnWith K f s) (hb : ∀ x ∈ s, |f x| ≤ B) :
    ∃ F : E → ℝ, LipschitzWith K F ∧ (∀ x, |F x| ≤ B) ∧ EqOn f F s := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_real
  refine ⟨fun x => min B (max (-B) (F x)),
    (hF.const_max (-B)).const_min B, ?_, ?_⟩
  · intro x
    apply abs_le.mpr
    exact ⟨le_min (by linarith : -B ≤ B) (le_max_left _ _), min_le_left _ _⟩
  · intro x hx
    change f x = min B (max (-B) (F x))
    rw [← hEq hx, max_eq_right (abs_le.mp (hb x hx)).1,
      min_eq_right (abs_le.mp (hb x hx)).2]

private theorem gaussian_ae_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ x ∂stdGaussian (Vector n), x ≠ 0 := by
  let : NeZero n := ⟨by omega⟩
  have hac : stdGaussian (Vector n) ≪ (volume : Measure (Vector n)) := by
    rw [GaussianDensity.stdGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  apply hac.ae_le
  exact (ae_iff).mpr (by simp)

private theorem angularLift_aestronglyMeasurable {n : ℕ} (hn : 1 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L) :
    AEStronglyMeasurable (angularLift g) (stdGaussian (Vector n)) := by
  have hi := geodesic_comp_integrable hn hg id continuous_id
  rw [unitSphereLaw_eq_normalizedGaussian hn] at hi
  exact (hi.comp_measurable (by fun_prop)).aestronglyMeasurable

private theorem bounded_exponentialEntropy_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (B : ℝ)
    (hFm : ∀ k, AEStronglyMeasurable (F k) μ)
    (hfm : AEStronglyMeasurable f μ)
    (hFB : ∀ k, ∀ᵐ x ∂μ, |F k x| ≤ B)
    (hfB : ∀ᵐ x ∂μ, |f x| ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (f x))) :
    Tendsto
      (fun k => (∫ x, Real.exp (F k x) * F k x ∂μ) -
        (∫ x, Real.exp (F k x) ∂μ) * Real.log (∫ x, Real.exp (F k x) ∂μ))
      atTop (𝓝 ((∫ x, Real.exp (f x) * f x ∂μ) -
        (∫ x, Real.exp (f x) ∂μ) * Real.log (∫ x, Real.exp (f x) ∂μ))) := by
  have hMass : Tendsto (fun k => ∫ x, Real.exp (F k x) ∂μ) atTop
      (𝓝 (∫ x, Real.exp (f x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => Real.exp B)
    · intro k
      exact Real.continuous_exp.comp_aestronglyMeasurable (hFm k)
    · exact integrable_const _
    · intro k
      filter_upwards [hFB k] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
    · filter_upwards [hlim] with x hx
      exact Real.continuous_exp.continuousAt.tendsto.comp hx
  have hFirst : Tendsto (fun k => ∫ x, Real.exp (F k x) * F k x ∂μ) atTop
      (𝓝 (∫ x, Real.exp (f x) * f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => Real.exp B * B)
    · intro k
      exact (Real.continuous_exp.comp_aestronglyMeasurable (hFm k)).mul (hFm k)
    · exact integrable_const _
    · intro k
      filter_upwards [hFB k] with x hx
      have he : Real.exp (F k x) ≤ Real.exp B :=
        Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
        mul_le_mul he hx (abs_nonneg (F k x)) (Real.exp_pos B).le
    · filter_upwards [hlim] with x hx
      exact (Real.continuous_exp.continuousAt.tendsto.comp hx).mul hx
  have hi : Integrable (fun x => Real.exp (f x)) μ := by
    apply Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable hfm)
      (Real.exp B)
    filter_upwards [hfB] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
  exact hFirst.sub (hMass.mul (hMass.log (integral_exp_pos hi).ne'))

private theorem fderiv_eq_of_eqOn_exterior {n : ℕ} {f F : Vector n → ℝ}
    {r : ℝ} (he : EqOn f F {y | r < ‖y‖}) {x : Vector n} (hx : r < ‖x‖) :
    fderiv ℝ f x = fderiv ℝ F x := by
  have ho : IsOpen {y : Vector n | r < ‖y‖} :=
    isOpen_lt continuous_const continuous_norm
  have hlocal : f =ᶠ[𝓝 x] F := by
    filter_upwards [ho.mem_nhds hx] with y hy
    exact he hy
  exact hlocal.fderiv_eq

/-- Actual globally Lipschitz approximation of every admitted angular
lift. Entropy and integrated derivative energy both converge, with no
analytic approximation premise. The shrinking-ball modification uses a
bounded Lipschitz extension; no smoothness of the sphere observable is needed. -/
theorem angularLift_bounded_lipschitz_approximation {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) :
    ∃ (B : ℝ) (F : ℕ → Vector n → ℝ), 0 ≤ B ∧
      (∀ k, ∃ K : ℝ≥0, LipschitzWith K (F k)) ∧
      (∀ k x, |F k x| ≤ B) ∧
      (∀ k, EqOn (angularLift g) (F k)
        {x | 1 / ((k : ℝ) + 1) < ‖x‖}) ∧
      Tendsto (fun k => gaussianEntropy (F k)) atTop
        (𝓝 (gaussianEntropy (angularLift g))) ∧
      Tendsto (fun k => gaussianEnergy (F k)) atTop
        (𝓝 (gaussianEnergy (angularLift g))) := by
  obtain ⟨B, hB, hb⟩ := angularLift_bounded hg
  let r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by dsimp only [r]; positivity
  have hrlim : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let C : ℝ := 2 * (Real.pi + 1) * L
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hLC : L ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg Real.pi_pos.le hL]
  have hext (k : ℕ) : ∃ F : Vector n → ℝ,
      LipschitzWith (Real.toNNReal (C / r k)) F ∧
        (∀ x, |F x| ≤ B) ∧ EqOn (angularLift g) F {x | r k < ‖x‖} :=
    exists_bounded_lipschitz_extension hB
      (angularLift_lipschitzOn_away_zero hL hg (hr k)) (fun x _ => hb x)
  choose F hF hbF heF using hext
  have hFderiv (k : ℕ) (x : Vector n) (hx : x ≠ 0) :
      ‖fderiv ℝ (F k) x‖ ≤ C / ‖x‖ := by
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    by_cases he : r k < ‖x‖
    · rw [← fderiv_eq_of_eqOn_exterior (heF k) he]
      exact (angularLift_fderiv_norm_le hL hg x hx).trans
        (div_le_div_of_nonneg_right hLC hxpos.le)
    · have hglobal := norm_fderiv_le_of_lipschitz ℝ (hF k) (x₀ := x)
      rw [Real.coe_toNNReal _ (div_nonneg hC (hr k).le)] at hglobal
      exact hglobal.trans (div_le_div_of_nonneg_left hC hxpos (le_of_not_gt he))
  have hevent (x : Vector n) (hx : x ≠ 0) : ∀ᶠ k in atTop, r k < ‖x‖ :=
    hrlim.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))
  have hlim : ∀ᵐ x ∂stdGaussian (Vector n),
      Tendsto (fun k => F k x) atTop (𝓝 (angularLift g x)) := by
    filter_upwards [gaussian_ae_ne_zero (by omega : 1 ≤ n)] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent x hx] with k hk
    exact heF k hk
  have hent : Tendsto (fun k => gaussianEntropy (F k)) atTop
      (𝓝 (gaussianEntropy (angularLift g))) :=
    bounded_exponentialEntropy_tendsto (stdGaussian (Vector n)) F (angularLift g) B
      (fun k => (hF k).continuous.aestronglyMeasurable)
      (angularLift_aestronglyMeasurable (by omega) hg)
      (fun k => Eventually.of_forall (hbF k)) (Eventually.of_forall hb) hlim
  have henergy : Tendsto (fun k => gaussianEnergy (F k)) atTop
      (𝓝 (gaussianEnergy (angularLift g))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x : Vector n => (Real.exp B * C ^ 2) * (‖x‖ ^ 2)⁻¹)
    · intro k
      exact ((hF k).continuous.rexp.aestronglyMeasurable).mul
        (((measurable_fderiv ℝ (F k)).norm.pow_const 2).aestronglyMeasurable)
    · exact (gaussian_inverse_norm_sq_integrable hn).const_mul _
    · intro k
      filter_upwards [gaussian_ae_ne_zero (by omega : 1 ≤ n)] with x hx
      rw [Real.norm_of_nonneg (by positivity)]
      have he : Real.exp (F k x) ≤ Real.exp B :=
        Real.exp_le_exp.mpr ((le_abs_self _).trans (hbF k x))
      have hd := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ (F k) x))
        (hFderiv k x hx) 2
      calc
        _ ≤ Real.exp B * (C / ‖x‖) ^ 2 :=
          mul_le_mul he hd (sq_nonneg _) (Real.exp_pos _).le
        _ = _ := by rw [div_pow]; ring
    · filter_upwards [gaussian_ae_ne_zero (by omega : 1 ≤ n)] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent x hx] with k hk
      rw [← heF k hk, ← fderiv_eq_of_eqOn_exterior (heF k) hk]
  exact ⟨B, F, hB, fun k => ⟨_, hF k⟩, hbF, heF, hent, henergy⟩

private theorem angularLift_gaussian_lsi_of_bounded_lipschitz
    (hGross : BoundedLipschitzGaussianLogSobolev) {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) :
    gaussianEntropy (angularLift g) ≤ (1 / 2 : ℝ) * gaussianEnergy (angularLift g) := by
  obtain ⟨B, F, _, hF, hbF, _, hent, henergy⟩ :=
    angularLift_bounded_lipschitz_approximation hn hL hg
  apply le_of_tendsto_of_tendsto hent (henergy.const_mul (1 / 2 : ℝ))
  apply Eventually.of_forall
  intro k
  obtain ⟨K, hK⟩ := hF k
  exact hGross n (F k) K hK ⟨B, hbF k⟩

/-- Complete reduction of the literal sphere interface to the bounded
globally Lipschitz Gaussian Gross inequality. All radial normalization,
sharp angular energy, and approximation steps are proved. The premise
is the remaining unproved functional inequality, not a sphere interface. -/
theorem bakryEmerySphereLogSobolev_of_bounded_lipschitz_gaussian
    (hGross : BoundedLipschitzGaussianLogSobolev) : BakryEmerySphereLogSobolev := by
  intro n hn g L hL hg t
  have htg : GeodesicLipschitz (fun x => t * g x) (|t| * L) := by
    intro x y hx hy
    calc
      |t * g x - t * g y| = |t| * |g x - g y| := by rw [← mul_sub, abs_mul]
      _ ≤ |t| * (L * Real.arccos (inner ℝ x y)) :=
        mul_le_mul_of_nonneg_left (hg x y hx hy) (abs_nonneg t)
      _ = _ := by ring
  have hgauss := angularLift_gaussian_lsi_of_bounded_lipschitz hGross hn
    (mul_nonneg (abs_nonneg t) hL) htg
  rw [exponential_entropy_eq_gaussian (by omega : 1 ≤ n) hg t]
  exact hgauss.trans (gaussian_half_energy_le_sphere_lsi_rhs hn hL hg t)

/-- `lem:ent-lsi` with no sphere LSI premise. Only the explicitly named
bounded globally Lipschitz Gaussian inequality remains in this reduction. -/
theorem geodesic_lipschitz_centered_mgf_reduced
    (hGross : BoundedLipschitzGaussianLogSobolev) {m : ℕ} (hm : 2 ≤ m)
    (g : Vector (m+1) → ℝ) {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L)
    (t : ℝ) :
    (∫ x, Real.exp (t * (g x - ∫ y, g y ∂unitSphereLaw (m+1)))
      ∂unitSphereLaw (m+1)) ≤ Real.exp (L ^ 2 * t ^ 2 / (2 * ((m : ℝ) - 1))) :=
  geodesic_lipschitz_centered_mgf
    (bakryEmerySphereLogSobolev_of_bounded_lipschitz_gaussian hGross) hm g hL hg t

/-- Both clauses of `lem:ent-latitude`, on the repository's original
Gaussian-bank good event, with the sphere interface replaced by the
single remaining Gaussian Gross premise. -/
theorem center_latitude_mean_and_mgf_reduced
    (hGross : BoundedLipschitzGaussianLogSobolev)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) :=
  center_latitude_mean_and_mgf
    (bakryEmerySphereLogSobolev_of_bounded_lipschitz_gaussian hGross) μ hQ

end SlowEquilibration.SourceSphereLogSobolevProof
