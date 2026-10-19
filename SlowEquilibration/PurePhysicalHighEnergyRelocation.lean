-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureHighEnergyRegularity
public import SlowEquilibration.PureHighEnergyCriticalHessian
public import SlowEquilibration.SphericalSuperlevelLocalization
public import SlowEquilibration.PureCapturePhysicalCoarseDiniAssembly

/-! Uniform high-energy relocation in manuscript `prop:pc-relocation`.
The original-disorder regularity, high-critical Hessian, and ground
concentration events give one measurable event covering every starting
point. Superlevel localization produces a nearby critical maximizer, and
the quantitative Hessian margin makes it a nondegenerate local maximum.
The exponential endpoint then discharges `PhysicalHighEnergyRelocation`.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.PurePhysicalHighEnergyRelocation

open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows SphericalForm
open SphericalGaussianJet SphereHessian PureStationarity NegativeDefiniteOperators
open PairConditionalDeterminantMoments SphericalHessianMarginEvents
open PureHighEnergyRegularity PureHighEnergyMaximumConcentration PureHighEnergyCriticalHessian
open SphericalCriticalGeodesicDecay SphericalSuperlevelLocalization
open PureCapturePhysicalCoarseDiniAssembly
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

private lemma center_one (μ : FiniteMixture) :
    centerCoefficients (mixtureCoefficients μ) 1 = mixtureCoefficients μ := by
  funext k
  simp [centerCoefficients]

private lemma exp_dimension_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.exp (-a * (n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) := by
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.const_mul_atTop ha)

/-- The short-geodesic quadratic drop gives a literal local maximum at
every critical point with positive margin, including the chart poles. -/
private theorem field_localMax_of_margin {N P : ℕ}
    (hN : 2 ≤ N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ ρ : ℝ} (hC : 0 < C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hCrit : surfaceGradient (field c J) u = 0)
    (hMargin : sourceHessianMargin c κ J u) :
    IsLocalMaxOn (field c J) {z : Vector N | ‖z‖ ^ 2 = (N : ℝ)} u := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hNpos : 0 < n + 1 := by omega
  have hsqrt : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  have hdist : Continuous (sphereGeodesicDist u) := by
    unfold sphereGeodesicDist overlap
    fun_prop
  have hnear : ∀ᶠ w in 𝓝 u,
      sphereGeodesicDist u w < ρ * Real.sqrt (n+1 : ℕ) :=
    (isOpen_lt hdist continuous_const).mem_nhds (by
      simp only [mem_ofPred_eq, sphereGeodesicDist, overlap_self hNpos u hu,
        Real.arccos_one, mul_zero]
      positivity)
  filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with w hwDist hw
  change field c J w ≤ field c J u
  by_cases heq : w = u
  · exact heq ▸ le_rfl
  have hr := overlap_mem_Icc_of_norm_sq hNpos u w hu hw
  have hrlt : overlap u w < 1 := lt_of_le_of_ne hr.2 (by
    intro he
    exact heq (source_sphere_eq_of_overlap_one hNpos u w hu hw he).symm)
  have hθpos : 0 < Real.arccos (overlap u w) := Real.arccos_pos.mpr hrlt
  have hθle : Real.arccos (overlap u w) ≤ ρ := by
    apply (mul_le_mul_iff_right₀ hsqrt).mp
    simpa only [sphereGeodesicDist, mul_comm] using hwDist.le
  have hrpos : 0 < overlap u w := by
    rw [← Real.cos_arccos hr.1 hr.2]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [hθle.trans hρ1, Real.pi_gt_three]
  obtain ⟨v, hv, huv, hEnd⟩ :=
    sourceSphereGeodesic_reconstruction u w hu hw ⟨hrpos, hrlt⟩
  have H := field_geodesic_quadratic_drop hN c J hC hκ hρ hρ1 hρκ hThird
    u v hu hv huv hCrit hMargin (Real.arccos (overlap u w)) ⟨hθpos.le, hθle⟩
  rw [hEnd] at H
  exact H.trans (sub_le_self _ (by positivity))

/-- Manuscript `prop:pc-relocation`: uniformly over every high-energy
point, relocation reaches a nondegenerate local maximum on one measurable
event whose complement is eventually exponentially small. -/
theorem pure_physical_relocation_exponential (p : ℕ) (hp : 4 ≤ p)
    {r : ℝ} (hr : 0 < r) :
    ∃ τ a : ℝ, 0 < τ ∧ 0 < a ∧
      ∃ Ω : ∀ n : ℕ,
          Set (Disorder (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree),
        (∀ n, MeasurableSet (Ω n)) ∧
        (∀ n, ∀ J ∈ Ω n, ∀ w : Vector (n+2),
          ‖w‖^2 = (n+2 : ℕ) →
          (n+2 : ℕ)*(pureEnergyConstant p (by omega)-τ) ≤
            field (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J w →
          ∃ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) ∧
            surfaceGradient
              (field (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J) u = 0 ∧
            IsLocalMaxOn
              (field (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J)
              {z | ‖z‖^2 = (n+2 : ℕ)} u ∧
            NegativeDefinite (intrinsicHessian
              (field (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J) u) ∧
            ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
            field (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J w ≤
              field (mixtureCoefficients (FiniteMixture.pure p (by omega) 1 (by positivity))) J u) ∧
        (∀ᶠ n : ℕ in atTop,
          (disorderLaw (n+2) (FiniteMixture.pure p (by omega) 1 (by positivity)).maxDegree).real
            (Ω n)ᶜ ≤ Real.exp (-a*(n+2 : ℕ))) := by
  let μ := FiniteMixture.pure p (by omega) 1 (by positivity)
  let e := pureEnergyConstant p (by omega)
  let κ := (p : ℝ) * (e - 2 * Real.sqrt (((p : ℝ)-1)/(p : ℝ))) / 4
  obtain ⟨C, hC, hThird⟩ := pure_original_spherical_third_bound p hp
  obtain ⟨hκ, t, b, ht, _, hb, hHmeas, hHprob⟩ := pure_all_high_critical_hessian p hp
  change 0 < κ at hκ
  let ρ := min (1 : ℝ) (κ / (2 * C))
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hκ (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρκ : 2 * C * ρ ≤ κ := by
    have hh : ρ ≤ κ / (2 * C) := min_le_right _ _
    nlinarith [(le_div_iff₀ (by positivity : 0 < 2 * C)).mp hh]
  let τ := min (t / 8) (min (κ * ρ^2 / 16) (κ * r^2 / 16))
  have hτ : 0 < τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hτt : τ ≤ t / 8 := min_le_left _ _
  have hτρ : τ ≤ κ * ρ^2 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hτr : τ ≤ κ * r^2 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 3 * τ < min (t / 2) (κ * ρ^2 / 4) := by
    apply lt_min <;> nlinarith
  have hrad : 2 * Real.sqrt (3 * τ / κ) ≤ r := by
    have hs := Real.sq_sqrt (show 0 ≤ 3 * τ / κ by positivity)
    have hdiv : 3 * τ / κ ≤ 3 * r^2 / 16 := by
      apply (div_le_iff₀ hκ).mpr
      nlinarith
    nlinarith [Real.sqrt_nonneg (3 * τ / κ)]
  let G (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) :=
    {J | |sourceSphereMaximum n μ 1 J / (n+2 : ℕ) - e| ≤ τ}
  let Ω (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) :=
    regularDisorder ∩ highCriticalMarginEvent n μ e t κ ∩ G n
  have hGmeas (n : ℕ) : MeasurableSet (G n) :=
    (isClosed_le (((sourceSphereMaximum_continuous n μ 1).div_const _).sub
      continuous_const).abs continuous_const).measurableSet
  let a := min 1 (min b (τ^2 / 8)) / 2
  have ha : 0 < a := half_pos (lt_min (by norm_num) (lt_min hb (by positivity)))
  have ha1 : 2*a ≤ 1 := by dsimp [a]; linarith [min_le_left (1 : ℝ) (min b (τ^2/8))]
  have hab : 2*a ≤ b := by
    dsimp [a]
    linarith [(min_le_right (1 : ℝ) (min b (τ^2/8))).trans (min_le_left _ _)]
  have haτ : 2*a ≤ τ^2/8 := by
    dsimp [a]
    linarith [(min_le_right (1 : ℝ) (min b (τ^2/8))).trans (min_le_right _ _)]
  refine ⟨τ, a, hτ, ha, Ω, ?_, ?_, ?_⟩
  · intro n
    exact ((regularDisorder_measurable _ _).inter (hHmeas n)).inter (hGmeas n)
  · intro n J hJ w hw henergy
    obtain ⟨⟨hReg, hHess⟩, hGround⟩ := hJ
    have hNr : (0 : ℝ) < (n+2 : ℕ) := by positivity
    let M := sSup ((field (mixtureCoefficients μ) J) ''
      {x : Vector (n+2) | ‖x‖^2 = (n+2 : ℕ)})
    have hM : sourceSphereMaximum n μ 1 J = M := by
      simp only [sourceSphereMaximum, center_one, M]
    change |sourceSphereMaximum n μ 1 J / (n+2 : ℕ) - e| ≤ τ at hGround
    rw [hM] at hGround
    have hMlo : (n+2 : ℕ) * (e-τ) ≤ M := by
      have hh := (abs_le.mp hGround).1
      simpa only [mul_comm] using
        (le_div_iff₀ hNr).mp (show e-τ ≤ M / (n+2 : ℕ) by linarith)
    have hMhi : M ≤ (n+2 : ℕ) * (e+τ) := by
      have hh := (abs_le.mp hGround).2
      simpa only [mul_comm] using
        (div_le_iff₀ hNr).mp (show M / (n+2 : ℕ) ≤ e+τ by linarith)
    have hMargins : ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
        surfaceGradient (field (mixtureCoefficients μ) J) u = 0 →
        M - (t/2) * (n+2 : ℕ) < field (mixtureCoefficients μ) J u →
        sourceHessianMargin (mixtureCoefficients μ) κ J u := by
      intro u hu hcrit hhigh
      apply hHess u hu hcrit
      have hh := mul_le_mul_of_nonneg_right (show τ + t/2 ≤ t by linarith) hNr.le
      nlinarith
    have hhigh : M - 3*τ*(n+2 : ℕ) < field (mixtureCoefficients μ) J w := by
      have hh := mul_pos hτ hNr
      nlinarith
    obtain ⟨u, huV, hcrit, hmargin, hmax, _, hdist⟩ :=
      field_superlevel_component_localization (by omega) (mixtureCoefficients μ) J
        hC hκ (half_pos ht) (show 0 < 3*τ by positivity)
        (hThird (n+2) (by omega) J hReg) hMargins hsmall w hw hhigh
    have hu : ‖u‖^2 = (n+2 : ℕ) := (connectedComponentIn_subset _ _ huV).1
    have hwV := mem_connectedComponentIn (show
      w ∈ {x : Vector (n+2) | ‖x‖^2 = (n+2 : ℕ) ∧
        M - 3*τ*(n+2 : ℕ) < field (mixtureCoefficients μ) J x} from ⟨hw, hhigh⟩)
    refine ⟨u, hu, hcrit, ?_, ?_, ?_, hmax w hwV⟩
    · exact field_localMax_of_margin (by omega) (mixtureCoefficients μ) J
        hC hκ hρ hρ1 hρκ (hThird (n+2) (by omega) J hReg) u hu hcrit hmargin
    · exact sourceHessianMargin_negative (by omega) (mixtureCoefficients μ) hκ J u hu hmargin
    · exact (norm_sub_le_sphereGeodesicDist (by omega) u w hu hw).trans
        ((hdist w hwV).2.le.trans
          (mul_le_mul_of_nonneg_right hrad (Real.sqrt_nonneg _)))
  · have hAbsorb : ∀ᶠ n : ℕ in atTop, 4*Real.exp (-a*(n+2 : ℕ)) ≤ 1 := by
      have hh := (exp_dimension_tendsto_zero ha).const_mul 4
      have hh' : Tendsto (fun n : ℕ => 4*Real.exp (-a*(n+2 : ℕ)))
          atTop (𝓝 (0 : ℝ)) := by simpa only [mul_zero] using hh
      exact (hh'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ h => h.le)
    filter_upwards [hHprob, pure_original_ground_concentration p hp hτ, hAbsorb]
      with n hH hG hAbs
    have hProb : (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤
        Real.exp (-(n+2 : ℕ)) + Real.exp (-b*(n+2 : ℕ)) +
          2*Real.exp (-(n+2 : ℕ)*τ^2/8) := by
      have hSub : (Ω n)ᶜ ⊆
          (regularDisorderᶜ ∪ (highCriticalMarginEvent n μ e t κ)ᶜ) ∪ (G n)ᶜ := by
        simp only [Ω, compl_inter]
        exact Subset.rfl
      have hGround : (disorderLaw (n+2) μ.maxDegree).real (G n)ᶜ ≤
          2*Real.exp (-(n+2 : ℕ)*τ^2/8) := by
        simpa only [G, compl_ofPred, not_le] using hG
      exact (measureReal_mono hSub (measure_ne_top _ _)).trans
        ((measureReal_union_le _ _).trans (add_le_add
          ((measureReal_union_le _ _).trans (add_le_add
            (regularDisorder_failure_probability (by omega)) hH)) hGround))
    have hNr : (0 : ℝ) ≤ (n+2 : ℕ) := by positivity
    have hRate₁ : -(n+2 : ℕ) ≤ -a*(n+2 : ℕ) + -a*(n+2 : ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_right ha1 hNr]
    have hRate₂ : -b*(n+2 : ℕ) ≤ -a*(n+2 : ℕ) + -a*(n+2 : ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_right hab hNr]
    have hRate₃ : -(n+2 : ℕ)*τ^2/8 ≤ -a*(n+2 : ℕ) + -a*(n+2 : ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_right haτ hNr]
    apply hProb.trans
    calc
      _ ≤ Real.exp (-a*(n+2 : ℕ) + -a*(n+2 : ℕ)) +
          Real.exp (-a*(n+2 : ℕ) + -a*(n+2 : ℕ)) +
          2*Real.exp (-a*(n+2 : ℕ) + -a*(n+2 : ℕ)) :=
        add_le_add (add_le_add (Real.exp_le_exp.mpr hRate₁) (Real.exp_le_exp.mpr hRate₂))
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hRate₃) (by norm_num))
      _ = (4*Real.exp (-a*(n+2 : ℕ))) * Real.exp (-a*(n+2 : ℕ)) := by
        rw [Real.exp_add]
        ring
      _ ≤ Real.exp (-a*(n+2 : ℕ)) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hAbs (Real.exp_pos _).le

/-- The exponential relocation theorem supplies the uniform physical
relocation premise used by the pure coarse-cover assembly. -/
theorem pure_physicalHighEnergyRelocation (p : ℕ) (hp : 4 ≤ p) :
    PhysicalHighEnergyRelocation
      (FiniteMixture.pure p (by omega) 1 (by positivity))
      (pureEnergyConstant p (by omega)) := by
  intro r hr
  obtain ⟨τ, a, hτ, ha, Ω, hMeas, hRelocate, hProb⟩ :=
    pure_physical_relocation_exponential p hp hr
  refine ⟨τ, hτ, Ω, hMeas, ?_, ?_⟩
  · intro n J hJ w hw henergy
    obtain ⟨u, hu, hcrit, _, _, hdist, himprove⟩ := hRelocate n J hJ w hw henergy
    exact ⟨u, hu, hcrit, hdist, himprove⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (exp_dimension_tendsto_zero ha)
      (Eventually.of_forall (fun _ => measureReal_nonneg)) hProb

end SlowEquilibration.PurePhysicalHighEnergyRelocation
