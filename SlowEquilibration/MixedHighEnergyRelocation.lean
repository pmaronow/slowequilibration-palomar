-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixedHighEnergyAllHigh
public import SlowEquilibration.SphericalSuperlevelLocalization

/-! Uniform center-field relocation in manuscript `lem:mb-localization`.
The simultaneous mixed all-high event and the above-contact maximum tail
give one measurable original-disorder event covering every starting point.
Deterministic superlevel localization moves each sufficiently high point to
a nearby critical local maximum with no loss of energy, a positive Hessian
margin, and radial mark in the prescribed interval. The resulting predicate
keeps the center field and the original disorder law distinct. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.MixedHighEnergyRelocation

open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows SphericalForm
open SphericalGaussianJet SphericalTAPCertificate TwoAtomStationarity
open PairConditionalDeterminantMoments SphericalHessianMarginEvents
open MixedHighEnergyAllHigh SphericalCriticalGeodesicDecay SphericalSuperlevelLocalization
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Radial-aware relocation for the center field, uniformly over all high
points on one measurable event under the original disorder law. -/
def CenterFieldRelocation (μ : FiniteMixture) (Q E : ℝ) (U : Set ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
      (∀ n, MeasurableSet (Ω n)) ∧
      (∀ n, ∀ J ∈ Ω n, ∀ w : Vector (n+2),
        ‖w‖^2 = (n+2 : ℕ) →
        (n+2 : ℕ)*(E-ε₀) ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J w →
        ∃ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) ∧
          surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 ∧
          actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U ∧
          ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
          field (centerCoefficients (mixtureCoefficients μ) Q) J w ≤
            field (centerCoefficients (mixtureCoefficients μ) Q) J u) ∧
      Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ)
        atTop (𝓝 (0 : ℝ))

/-- A positive margin and the short-geodesic drop give a local maximum
on the whole sphere, including points outside the manuscript chart. -/
private theorem field_localMax_of_margin {N P : ℕ}
    (hN : 2 ≤ N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ ρ : ℝ} (hC : 0 < C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖^2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u : Vector N) (hu : ‖u‖^2 = (N : ℝ))
    (hCrit : surfaceGradient (field c J) u = 0)
    (hMargin : sourceHessianMargin c κ J u) :
    IsLocalMaxOn (field c J) {z : Vector N | ‖z‖^2 = (N : ℝ)} u := by
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

/-- Manuscript `lem:mb-localization`: the relocated critical point is a
local maximum with a uniform positive Hessian margin and prescribed radial
mark. The same original-disorder event covers every eligible starting point. -/
theorem mixed_high_energy_relocation
    (μ : FiniteMixture) {β x Q L R r : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < L)
    (hL : L < markK μ β Q) (hR : markK μ β Q < R) (hr : 0 < r) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
      ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
        (∀ n, MeasurableSet (Ω n)) ∧
        (∀ n, ∀ J ∈ Ω n, ∀ w : Vector (n+2),
          ‖w‖^2 = (n+2 : ℕ) →
          (n+2 : ℕ)*(markE μ β x Q-ε₀) ≤
            field (centerCoefficients (mixtureCoefficients μ) Q) J w →
          ∃ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) ∧
            surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 ∧
            actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R ∧
            sourceHessianMargin (centerCoefficients (mixtureCoefficients μ) Q) κ J u ∧
            IsLocalMaxOn (field (centerCoefficients (mixtureCoefficients μ) Q) J)
              {z | ‖z‖^2 = (n+2 : ℕ)} u ∧
            ‖u-w‖ ≤ r*Real.sqrt (n+2 : ℕ) ∧
            field (centerCoefficients (mixtureCoefficients μ) Q) J w ≤
              field (centerCoefficients (mixtureCoefficients μ) Q) J u) ∧
        Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ)
          atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨δ₀, κ, C, c, hδ₀, hκ, hC, hc, A, hMeas, hAll, hProb⟩ :=
    mixed_all_high_critical_event μ h hnp hEdge hL hR
  let ρ := min (1 : ℝ) (κ / (2 * C))
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos hκ (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρκ : 2 * C * ρ ≤ κ := by
    have hh : ρ ≤ κ / (2 * C) := min_le_right _ _
    nlinarith [(le_div_iff₀ (by positivity : 0 < 2 * C)).mp hh]
  let ε₀ := min (δ₀ / 8) (min (κ * ρ^2 / 16) (κ * r^2 / 16))
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεδ : ε₀ ≤ δ₀ / 8 := min_le_left _ _
  have hερ : ε₀ ≤ κ * ρ^2 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε₀ ≤ κ * r^2 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 3 * ε₀ < min (δ₀ / 2) (κ * ρ^2 / 4) := by
    apply lt_min <;> nlinarith
  have hrad : 2 * Real.sqrt (3 * ε₀ / κ) ≤ r := by
    have hs := Real.sq_sqrt (show 0 ≤ 3 * ε₀ / κ by positivity)
    have hdiv : 3 * ε₀ / κ ≤ 3 * r^2 / 16 := by
      apply (div_le_iff₀ hκ).mpr
      nlinarith
    nlinarith [Real.sqrt_nonneg (3 * ε₀ / κ)]
  let G (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) :=
    {J | sourceSphereMaximum n μ Q J ≤ (n+2 : ℕ)*(markE μ β x Q+ε₀)}
  let Ω (n : ℕ) := A n ∩ G n
  have hGmeas (n : ℕ) : MeasurableSet (G n) :=
    (isClosed_le (sourceSphereMaximum_continuous n μ Q) continuous_const).measurableSet
  refine ⟨ε₀, κ, hε₀, hκ, Ω, fun n => (hMeas n).inter (hGmeas n), ?_, ?_⟩
  · intro n J hJ w hw henergy
    obtain ⟨hA, hGround⟩ := hJ
    obtain ⟨hHigh, hThird, _⟩ := hAll n J hA
    let cQ := centerCoefficients (mixtureCoefficients μ) Q
    let E := markE μ β x Q
    let M := sourceSphereMaximum n μ Q J
    have hNr : (0 : ℝ) < (n+2 : ℕ) := by positivity
    have hMlo : (n+2 : ℕ)*(E-ε₀) ≤ M := by
      apply henergy.trans
      obtain ⟨v, _, _, hMax, hValue⟩ := sourceSphereMaximum_attained n μ Q J
      change field cQ J w ≤ sourceSphereMaximum n μ Q J
      rw [hValue]
      exact hMax hw
    have hMhi : M ≤ (n+2 : ℕ)*(E+ε₀) := hGround
    have hMargins : ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
        surfaceGradient (field cQ J) u = 0 →
        M - (δ₀/2)*(n+2 : ℕ) < field cQ J u → sourceHessianMargin cQ κ J u := by
      intro u hu hcrit hhigh
      apply (hHigh u hu hcrit ?_).2
      have hh := mul_le_mul_of_nonneg_right (show ε₀ + δ₀/2 ≤ δ₀ by linarith) hNr.le
      nlinarith
    have hhigh : M - 3*ε₀*(n+2 : ℕ) < field cQ J w := by
      have hh := mul_pos hε₀ hNr
      nlinarith
    obtain ⟨u, huV, hcrit, hmargin, hmax, _, hdist⟩ :=
      field_superlevel_component_localization (by omega) cQ J
        hC hκ (half_pos hδ₀) (show 0 < 3*ε₀ by positivity)
        hThird hMargins hsmall w hw hhigh
    have hu : ‖u‖^2 = (n+2 : ℕ) := (connectedComponentIn_subset _ _ huV).1
    have hwV := mem_connectedComponentIn (show
      w ∈ {z : Vector (n+2) | ‖z‖^2 = (n+2 : ℕ) ∧
        M - 3*ε₀*(n+2 : ℕ) < field cQ J z} from ⟨hw, hhigh⟩)
    have himprove : field cQ J w ≤ field cQ J u := hmax w hwV
    have huHigh : (n+2 : ℕ)*(E-δ₀) ≤ field cQ J u := by
      have hh := mul_le_mul_of_nonneg_left (show E-δ₀ ≤ E-ε₀ by linarith) hNr.le
      exact hh.trans (henergy.trans himprove)
    refine ⟨u, hu, hcrit, (hHigh u hu hcrit huHigh).1, hmargin, ?_, ?_, himprove⟩
    · exact field_localMax_of_margin (by omega) cQ J
        hC hκ hρ hρ1 hρκ hThird u hu hcrit hmargin
    · exact (norm_sub_le_sphereGeodesicDist (by omega) u w hu hw).trans
        ((hdist w hwV).2.le.trans
          (mul_le_mul_of_nonneg_right hrad (Real.sqrt_nonneg _)))
  · have hExp : Tendsto (fun n : ℕ => C * Real.exp (-c*(n+2 : ℕ)))
        atTop (𝓝 (0 : ℝ)) := by
      have hh : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) :=
        Real.tendsto_exp_atBot.comp
          ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)).const_mul_atTop_of_neg
            (neg_neg_of_pos hc))
      simpa only [mul_zero] using hh.const_mul C
    have hAZero : Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (A n)ᶜ)
        atTop (𝓝 (0 : ℝ)) :=
      squeeze_zero' (.of_forall (fun _ => measureReal_nonneg)) hProb hExp
    have hGZero : Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (G n)ᶜ)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [G, compl_ofPred, not_le] using
        mixed_center_maximum_above_contact_tendsto_zero μ h hnp ε₀ hε₀
    apply squeeze_zero' (.of_forall (fun _ => measureReal_nonneg)) _
      (show Tendsto (fun n => (disorderLaw (n+2) μ.maxDegree).real (A n)ᶜ +
        (disorderLaw (n+2) μ.maxDegree).real (G n)ᶜ) atTop (𝓝 (0 : ℝ)) by
          simpa only [add_zero] using hAZero.add hGZero)
    exact .of_forall fun n => by
      change (disorderLaw (n+2) μ.maxDegree).real (A n ∩ G n)ᶜ ≤ _
      rw [compl_inter]
      exact measureReal_union_le _ _

/-- The radial-aware center-field relocation predicate needed by the mixed
coarse-cover assembly follows from the certificate and the all-high inputs. -/
theorem mixed_centerFieldRelocation
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < L)
    (hL : L < markK μ β Q) (hR : markK μ β Q < R) :
    CenterFieldRelocation μ Q (markE μ β x Q) (Ioo L R) := by
  intro r hr
  obtain ⟨ε₀, κ, hε₀, _, Ω, hMeas, hRelocate, hProb⟩ :=
    mixed_high_energy_relocation μ h hnp hEdge hL hR hr
  refine ⟨ε₀, hε₀, Ω, hMeas, ?_, hProb⟩
  intro n J hJ w hw henergy
  obtain ⟨u, hu, hcrit, hradial, _, _, hdist, himprove⟩ :=
    hRelocate n J hJ w hw henergy
  exact ⟨u, hu, hcrit, hradial, hdist, himprove⟩

end SlowEquilibration.MixedHighEnergyRelocation
