-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePressure
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

/-! Uniform actual latitude pressure upper estimates. A finite open cover
reduces a compact continuum of trial parameters to genuine fixed Gaussian
linear endpoints. No uniform pressure-limit hypothesis is used. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def latitudePressureCorrection (μ : FiniteMixture) (β q : ℝ) : ℝ :=
  β^2/2*(μ.xi 1-μ.xi q-(1-q)*μ.xi1 q)

theorem latitudeLimitingVariance_continuous (μ : FiniteMixture) (β : ℝ) :
    Continuous (latitudeLimitingVariance μ β) := by
  have hxi : Continuous μ.xi1 := continuous_iff_continuousAt.mpr
    (fun r => (μ.hasDerivAt_xi1 r).continuousAt)
  exact (continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).mul hxi

theorem latitudePressureCorrection_continuous (μ : FiniteMixture) (β : ℝ) :
    Continuous (latitudePressureCorrection μ β) := by
  have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr
    (fun r => (μ.hasDerivAt_xi r).continuousAt)
  have hxi1 : Continuous μ.xi1 := continuous_iff_continuousAt.mpr
    (fun r => (μ.hasDerivAt_xi1 r).continuousAt)
  exact continuous_const.mul ((continuous_const.sub hxi).sub
    ((continuous_const.sub continuous_id).mul hxi1))

theorem latitudePressureTrial_continuousAt (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : 0 ≤ q) : ContinuousAt (latitudePressureTrial μ β) q := by
  have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr
    (fun r => (μ.hasDerivAt_xi r).continuousAt)
  have hlog : ContinuousAt (fun r : ℝ => Real.log (1+r)) q :=
    (continuousAt_const.add continuousAt_id).log (by change 1+q ≠ 0; linarith)
  exact (((continuousAt_const.mul (continuousAt_const.sub hxi.continuousAt)).add
    continuousAt_id).sub hlog).div_const 2

theorem latitudeLinearVariance_eq {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture) (β q : ℝ) :
    latitudeLinearVariance n μ β q = latitudeLimitingVariance μ β q*(1+1/(n : ℝ)) := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold latitudeLinearVariance latitudeLimitingVariance
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

/-- Compactly uniform mean upper for the genuine latitude partitions. The
finite open cover and all Gaussian-shell thresholds are independent of the
physical center, tangent frame and latitude selected from the compact set. -/
theorem latitudeQuenchedPressure_eventually_uniform_upper_of_tangent
    (μ : FiniteMixture) (β : ℝ) (S : Set ℝ) (hS : IsCompact S)
    (hSrange : S ⊆ Icc 0 1)
    (htangent : ∀ q ∈ S, ∀ t ∈ Icc (-1 : ℝ) 1,
      μ.xi q+μ.xi1 q*(q^2+(1-q^2)*t-q) ≤ μ.xi (q^2+(1-q^2)*t))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ S, ∀ (u : Vector (n+1)), ‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)), (∀ x, inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤ latitudePressureTrial μ β q+ε := by
  classical
  let δ : S → ℝ := fun c => ε*(1+(c : ℝ))/4
  let K : S → ℝ := fun c => latitudeLimitingVariance μ β c+δ c
  have hδ (c : S) : 0 < δ c := by
    have hc := hSrange c.property
    have hc0 : 0 ≤ (c : ℝ) := hc.1
    dsimp [δ]
    positivity
  have hK (c : S) : 0 ≤ K c := by
    dsimp [K]
    exact add_nonneg (latitudeLimitingVariance_nonneg μ β (hSrange c.property)) (hδ c).le
  have hloc : ∀ c : S, ∃ r : ℝ, 0 < r ∧ ∀ q : ℝ, dist q (c : ℝ) < r →
      latitudeLimitingVariance μ β q < K c-δ c/2 ∧
      quenchedLinearTrial (K c) (1+c)+latitudePressureCorrection μ β q <
        latitudePressureTrial μ β q+ε/2 := by
    intro c
    have hc := hSrange c.property
    have hVar := (latitudeLimitingVariance_continuous μ β).continuousAt.eventually
      (gt_mem_nhds (show latitudeLimitingVariance μ β c < K c-δ c/2 by
        dsimp [K]; linarith [hδ c]))
    have hT : ContinuousAt (fun q => latitudePressureTrial μ β q-
      latitudePressureCorrection μ β q) (c : ℝ) :=
      (latitudePressureTrial_continuousAt μ β hc.1).sub
        (latitudePressureCorrection_continuous μ β).continuousAt
    have heq : quenchedLinearTrial (K c) (1+c)+latitudePressureCorrection μ β c =
        latitudePressureTrial μ β c+ε/8 := by
      have hz : 1+(c : ℝ) ≠ 0 := ne_of_gt (by linarith [hc.1])
      have hv := latitude_linear_trial_eval μ β hc.1
      change quenchedLinearTrial (K c) (1+c)+latitudePressureCorrection μ β c = _
      rw [← hv]
      dsimp [K, δ]
      unfold quenchedLinearTrial latitudePressureCorrection
      field_simp
      ring
    have hval : quenchedLinearTrial (K c) (1+c)-ε/2 <
        latitudePressureTrial μ β c-latitudePressureCorrection μ β c := by linarith
    have hnear := hT.eventually (lt_mem_nhds hval)
    have hall : ∀ᶠ q : ℝ in 𝓝 (c : ℝ),
        latitudeLimitingVariance μ β q < K c-δ c/2 ∧
        quenchedLinearTrial (K c) (1+c)+latitudePressureCorrection μ β q <
          latitudePressureTrial μ β q+ε/2 := by
      filter_upwards [hVar, hnear] with q hVar hnear
      exact ⟨hVar, by linarith⟩
    exact Metric.eventually_nhds_iff.mp hall
  choose r hr hnear using hloc
  obtain ⟨T, hcover⟩ := hS.elim_finite_subcover
    (fun c : S => Metric.ball (c : ℝ) (r c)) (fun _ => Metric.isOpen_ball) (by
      intro q hq
      exact mem_iUnion.mpr ⟨⟨q,hq⟩, by simpa using hr ⟨q,hq⟩⟩)
  have hevent : ∀ c ∈ T, ∀ᶠ n : ℕ in atTop,
      linearSphereQuenchedPressure n (K c) ≤ quenchedLinearTrial (K c) (1+c)+ε/4 ∧
      K c/(n : ℝ) < δ c/2 := by
    intro c _
    have hlin := linearSphereQuenchedPressure_eventually_upper (hK c)
      (show 1 ≤ 1+(c : ℝ) by linarith [(hSrange c.property).1]) (by positivity : 0 < ε/4)
    have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (K c)).eventually
      (gt_mem_nhds (div_pos (hδ c) (by norm_num : (0 : ℝ) < 2)))
    exact hlin.and hsmall
  filter_upwards [T.eventually_all.mpr hevent, eventually_ge_atTop 1] with n hevent hn
  intro q hq u hu e he
  obtain ⟨c, hcT, hc⟩ := mem_iUnion₂.mp (hcover hq)
  obtain ⟨hVar, hlocal⟩ := hnear c q hc
  have hqr := hSrange hq
  have hκ : 0 ≤ latitudeLinearVariance n μ β q := latitudeLinearVariance_nonneg n μ β hqr
  have hVarK : latitudeLimitingVariance μ β q ≤ K c := by linarith [hδ c]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hdiff : latitudeLimitingVariance μ β q/(n : ℝ) ≤ K c/(n : ℝ) :=
    div_le_div_of_nonneg_right hVarK hn0.le
  have hκK : latitudeLinearVariance n μ β q ≤ K c := by
    rw [latitudeLinearVariance_eq hn μ β q]
    have hx : latitudeLimitingVariance μ β q*(1+1/(n : ℝ)) =
      latitudeLimitingVariance μ β q+latitudeLimitingVariance μ β q/(n : ℝ) := by ring
    rw [hx]
    linarith [(hevent c hcT).2]
  have hmono := linearSphereQuenchedPressure_mono hn hκ hκK
  have hlin := hmono.trans (hevent c hcT).1
  have hN0 : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hα0 : 0 ≤ (n : ℝ)/((n+1 : ℕ) : ℝ) := by positivity
  have hα1 : (n : ℝ)/((n+1 : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_one hN0).mpr
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hTpos : 0 ≤ quenchedLinearTrial (K c) (1+c)+ε/4 :=
    add_nonneg (quenchedLinearTrial_nonneg (hK c)
      (by linarith [(hSrange c.property).1])) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hlin hα0
  have hb := mul_le_mul_of_nonneg_right hα1 hTpos
  simp only [one_mul] at hb
  have hcomp := latitudeQuenchedPressure_le_linearTrial hn μ β hqr (htangent q hq) u hu e he
  change latitudeQuenchedPressure n μ β u e q ≤ _+latitudePressureCorrection μ β q at hcomp
  linarith

theorem latitudeQuenchedPressure_eventually_uniform_upper (μ : FiniteMixture) (β : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤ latitudePressureTrial μ β q+ε :=
  latitudeQuenchedPressure_eventually_uniform_upper_of_tangent μ β _ (isCompact_Icc)
    (fun _ hq => ⟨by linarith [hq.1], hq.2⟩)
    (fun q hq t ht => μ.xi_latitude_tangent_le hq ht) hε

theorem latitudeQuenchedPressure_eventually_uniform_upper_of_even
    (μ : FiniteMixture) (β : ℝ) (heven : ∀ p ∈ μ.coeff.support, Even p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (0 : ℝ) 1, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤ latitudePressureTrial μ β q+ε := by
  apply latitudeQuenchedPressure_eventually_uniform_upper_of_tangent μ β _ isCompact_Icc
    Subset.rfl _ hε
  intro q hq t ht
  have hs : 0 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  have harg : q^2+(1-q^2)*t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg hs (by linarith [ht.1] : 0 ≤ t+1),
      mul_nonneg hs (by linarith [ht.2] : 0 ≤ 1-t)]
  exact convex_covariance_supporting_line μ (μ.convexOn_xi_Icc_of_even heven)
    ⟨by linarith [hq.1], hq.2⟩ harg

/-- The actual planted mean upper holds simultaneously on the full interval
[one half, one], with a single dimension threshold. -/
theorem plantedLatitudeQuenchedPressure_eventually_uniform_upper (μ : FiniteMixture)
    {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (1/2 : ℝ) 1, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeQuenchedPressure n μ β u e q ≤
        (β^2*(μ.xi 1+μ.xi q)+q-Real.log (1+q))/2+ε := by
  filter_upwards [latitudeQuenchedPressure_eventually_uniform_upper μ β hε,
    eventually_ge_atTop 1] with n hn hdim
  intro q hq u hu e he
  have hh := hn q hq u hu e he
  rw [plantedLatitudeQuenchedPressure_eq hdim μ hβ u hu e he
    (abs_le.mpr ⟨by linarith [hq.1], hq.2⟩)]
  unfold latitudePressureTrial at hh
  linarith

theorem plantedLatitudeQuenchedPressure_eventually_uniform_upper_of_even
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (heven : ∀ p ∈ μ.coeff.support, Even p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (0 : ℝ) 1, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeQuenchedPressure n μ β u e q ≤
        (β^2*(μ.xi 1+μ.xi q)+q-Real.log (1+q))/2+ε := by
  filter_upwards [latitudeQuenchedPressure_eventually_uniform_upper_of_even μ β heven hε,
    eventually_ge_atTop 1] with n hn hdim
  intro q hq u hu e he
  have hh := hn q hq u hu e he
  rw [plantedLatitudeQuenchedPressure_eq hdim μ hβ u hu e he
    (abs_le.mpr ⟨by linarith [hq.1], hq.2⟩)]
  unfold latitudePressureTrial at hh
  linarith

end
end SlowEquilibration.SphericalModel
