-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCutoffMonotonicity

/-! The literal source collar and sharp scalar barrier for genuine finite
cutoffs, with all finite temperature and admissibility premises derived. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (μ : InfiniteMixture)

/-- Every compact interval in the actual strict superlevel is eventually
inside the genuine finite-cutoff strict superlevel, uniformly over the interval. -/
theorem basedCutoff_compact_superlevel_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    {β l u : ℝ} (hlu : l ≤ u)
    (hD : Icc l u ⊆ Thresholds.plateauSuperlevel μ.xi β) :
    ∀ᶠ n in atTop, Icc l u ⊆ Thresholds.plateauSuperlevel (μ.basedCutoff P₀ h₀ n).xi β := by
  have hphys : Icc l u ⊆ Icc (0:ℝ) 1 := fun r hr =>
    ⟨(hD hr).1.1.le,(hD hr).1.2.le⟩
  have hc : ContinuousOn (fun r => β^2*μ.A r) (Icc l u) :=
    (μ.continuousOn_A.mono (fun r hr => ⟨by linarith [(hphys hr).1],(hphys hr).2⟩)).const_mul _
  obtain ⟨z,hz,hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlu) hc
  have hzlevel : 1 < β^2*μ.A z := by
    rw [μ.A_eq_threshold (hD hz).1]
    exact (hD hz).2
  have hscaled := (uniformContinuous_mul_left' (β^2)).comp_tendstoUniformlyOn
    μ.cutoffA_tendstoUniformlyOn
  have he := Metric.tendstoUniformlyOn_iff.mp hscaled (β^2*μ.A z-1) (sub_pos.mpr hzlevel)
  have hindex : Tendsto (fun n => P₀+n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat P₀
  filter_upwards [hindex he] with n hn r hr
  refine ⟨(hD hr).1,?_⟩
  have hh := hn r (hphys hr)
  simp only [Function.comp_def,Real.dist_eq] at hh
  have hh' := (abs_lt.mp hh).2
  have hmin : β^2*μ.A z ≤ β^2*μ.A r := hm hr
  unfold basedCutoff
  rw [μ.finiteCutoff_A_eq _ _ (hD hr).1.1.ne']
  linarith

namespace CuspCoordinate
variable {μ} (c : CuspCoordinate μ)

/-- The fixed source collar is a literal admissible collar for all large
cutoffs, including the entire interval up to the moving finite `qStar`. -/
theorem basedCutoff_admissible_collar_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    (hgap : Thresholds.dynamicalThreshold μ.xi < Thresholds.staticThreshold μ.xi) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
      SphericalModel.IsAdmissibleCollar (μ.basedCutoff P₀ h₀ n)
        (c.epsilonTemperature ε) (c.collarLeft ε) (c.collarRight ε) := by
  filter_upwards [c.collar_eventually,c.epsilon_roots_eventually,
    c.basedCutoff_qStar_tendsto_eventually P₀ h₀,c.epsilonTemperature_window_eventually hgap]
    with ε hc he ht hw
  let b : ℝ := max (c.collarLeft ε) μ.qD
  have hcompact : Icc (c.collarLeft ε) b ⊆
      Thresholds.plateauSuperlevel μ.xi (c.epsilonTemperature ε) := by
    intro r hr
    apply hc.2.2.2.2.1
    refine ⟨hc.1.trans_le hr.1,hr.2.trans_lt ?_⟩
    exact max_lt (hc.2.1.trans hc.2.2.1) he.2.1
  have hlevel := μ.basedCutoff_compact_superlevel_eventually P₀ h₀
    (le_max_left (c.collarLeft ε) μ.qD) hcompact
  have htemp := μ.basedCutoff_temperature_window_eventually P₀ h₀ hw.1 hw.2
  filter_upwards [hlevel,htemp,c.basedCutoff_strictAntiOn_A_right_eventually P₀ h₀,
    ht.eventually (Ioi_mem_nhds hc.2.2.1),ht.eventually (Ioi_mem_nhds he.2.1)]
    with n hn hβ hanti hq₂ hqD
  have hq := (μ.basedCutoff P₀ h₀ n).qStar_solves_plateau hβ.1
  have hqle : Thresholds.qStar (μ.basedCutoff P₀ h₀ n).xi (c.epsilonTemperature ε) ≤ c.qPlus ε := by
    rw [← he.2.2.2.2.2.2]
    apply csSup_le ((μ.basedCutoff P₀ h₀ n).plateauSuperlevel_nonempty hβ.1)
    intro r hr
    exact le_csSup ⟨1,fun s hs => hs.1.2.le⟩
      (μ.basedCutoff_plateauSuperlevel_subset P₀ h₀ n _ hr)
  have hqR := hqle.trans hc.2.2.2.2.2.2
  refine ⟨he.2.2.1.1.trans hc.1,hc.2.1,hq₂,?_⟩
  intro r hr
  by_cases hrd : r ≤ μ.qD
  · exact (hn ⟨hr.1.le,hrd.trans (le_max_right _ _)⟩).2
  · have hrD : μ.qD ≤ r := (lt_of_not_ge hrd).le
    have hA := hanti ⟨hrD,hr.2.le.trans hqR⟩ ⟨hqD.le,hqR⟩ hr.2
    have hβpos := (μ.basedCutoff P₀ h₀ n).dynamicalThreshold_pos.trans hβ.1
    have hh := mul_lt_mul_of_pos_left hA (sq_pos_of_pos hβpos)
    rwa [(Thresholds.plateau_iff hq.1).mpr hq.2] at hh

/-- All scalar premises needed to choose a genuine finite model for the
source barrier, with the overlap and width retained independently of cutoff. -/
theorem basedCutoff_scalar_certificate_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    (hgap : Thresholds.dynamicalThreshold μ.xi < Thresholds.staticThreshold μ.xi)
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      μ.qD/2 < c.collarLeft ε ∧ c.collarRight ε-c.collarLeft ε=ε/2 ∧
      ∀ᶠ n in atTop,
        Thresholds.dynamicalThreshold (μ.basedCutoff P₀ h₀ n).xi < c.epsilonTemperature ε ∧
        c.epsilonTemperature ε < Thresholds.staticThreshold (μ.basedCutoff P₀ h₀ n).xi ∧
        SphericalModel.IsAdmissibleCollar (μ.basedCutoff P₀ h₀ n)
          (c.epsilonTemperature ε) (c.collarLeft ε) (c.collarRight ε) ∧
        (1-θ)*(c.barrierCoefficient*ε^(1+((2*c.m:ℕ):ℝ)⁻¹)) <
          SphericalModel.plantedCollarGap (μ.basedCutoff P₀ h₀ n)
            (c.epsilonTemperature ε) (c.collarRight ε) := by
  filter_upwards [c.collarLeft_above_half_eventually,
    c.basedCutoff_admissible_collar_eventually P₀ h₀ hgap,
    c.basedCutoff_collarGap_lower_eventually P₀ h₀ hθ,
    c.epsilonTemperature_window_eventually hgap] with ε hq hc hg hw
  refine ⟨hq,c.collar_width ε,?_⟩
  filter_upwards [hc,hg,μ.basedCutoff_temperature_window_eventually P₀ h₀ hw.1 hw.2]
    with n hn hg hβ
  exact ⟨hβ.1,hβ.2,hn,hg⟩

/-- A downstream selection theorem: the scalar certificate is available
beyond any other prescribed cutoff, allowing simultaneous tail requirements. -/
theorem exists_basedCutoff_scalar_certificate_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    (hgap : Thresholds.dynamicalThreshold μ.xi < Thresholds.staticThreshold μ.xi)
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ B : ℕ, ∃ n ≥ B,
      μ.qD/2 < c.collarLeft ε ∧ c.collarRight ε-c.collarLeft ε=ε/2 ∧
      Thresholds.dynamicalThreshold (μ.basedCutoff P₀ h₀ n).xi < c.epsilonTemperature ε ∧
      c.epsilonTemperature ε < Thresholds.staticThreshold (μ.basedCutoff P₀ h₀ n).xi ∧
      SphericalModel.IsAdmissibleCollar (μ.basedCutoff P₀ h₀ n)
        (c.epsilonTemperature ε) (c.collarLeft ε) (c.collarRight ε) ∧
      (1-θ)*(c.barrierCoefficient*ε^(1+((2*c.m:ℕ):ℝ)⁻¹)) <
        SphericalModel.plantedCollarGap (μ.basedCutoff P₀ h₀ n)
          (c.epsilonTemperature ε) (c.collarRight ε) := by
  filter_upwards [c.basedCutoff_scalar_certificate_eventually P₀ h₀ hgap hθ] with ε he B
  obtain ⟨n,hnB,hn⟩ := ((eventually_ge_atTop B).and he.2.2).exists
  exact ⟨n,hnB,he.1,he.2.1,hn⟩

end CuspCoordinate
end SlowEquilibration.InfiniteMixture
