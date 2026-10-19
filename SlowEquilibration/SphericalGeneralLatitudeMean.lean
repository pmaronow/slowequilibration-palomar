-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGeneralLatitudeGuerra
public import SlowEquilibration.SphericalLatitudeUniformMean

@[expose] public section

/-! # Genuine compact latitude mean upper for every finite mixture

The true odd-mixture finite Guerra bound is combined with the proved
Gaussian-shell linear endpoint through a finite compact cover. No
uniform pressure-limit or global covariance convexity is assumed.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual compactly uniform RS Dirac upper for all finite mixtures,
including odd degrees and a quadratic component, at every positive
latitude bounded away from the pole. -/
theorem general_latitudeQuenchedPressure_eventually_uniform_upper
    (μ : FiniteMixture) (β : ℝ) {δ ρ : ℝ} (hδ : 0<δ) (hδρ : δ≤ρ) (hρ : ρ<1)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ q∈Icc δ ρ,∀ (u : Vector (n+1)),‖u‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),(∀ x,inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q≤latitudePressureTrial μ β q+ε := by
  classical
  let S : Set ℝ := Icc δ ρ
  have hS : IsCompact S := isCompact_Icc
  have hSrange : S⊆Icc (0 : ℝ) 1 := by
    intro q hq
    exact ⟨hδ.le.trans hq.1,hq.2.trans hρ.le⟩
  have hcomparison := general_latitudeQuenchedPressure_eventually_le_linearTrial μ β hδ hδρ hρ
    (by positivity : 0<ε/4)
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
  filter_upwards [T.eventually_all.mpr hevent,hcomparison,eventually_ge_atTop 1] with n hevent hcomparison hn
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
  have hcomp := hcomparison q hq u hu e he
  change latitudeQuenchedPressure n μ β u e q ≤ _+latitudePressureCorrection μ β q+ε/4 at hcomp
  linarith

end
end SlowEquilibration.SphericalModel
