-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureDenominatorOriginal
public import SlowEquilibration.SphericalPureCapOriginalOutside

/-! Transfer the selected pure critical-band denominator estimate to any
cap mean having the full source annealed-scale asymptotic. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorFixedCapTransfer
noncomputable section
open Filter Set MeasureTheory SphericalModel SphericalTAPCertificate
open SphericalPureDenominatorScaleComparison
open SphericalTAPCriticalBandSectionBridge
open SphericalPureCapTailScale PureStationarity
open scoped Topology
set_option autoImplicit false

/-- A deterministic cap scale with a finite normalized limit inherits the
unconditional physical partition lower tail. -/
theorem pure_partition_cap_scale_denominator_lower_tail
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (A : ℕ → ℝ) (K : ℝ)
    (hA : Tendsto (fun n : ℕ => capScale (n+3)
      (CSParisiMeasure.variationalValue
        (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
      (1/(2*x))*A n) atTop (𝓝 K)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      Filter.limsup (fun n : ℕ =>
        (disorderLaw (n+3) μ.maxDegree).real
          {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
            η*A n}) atTop ≤ ε := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  obtain ⟨m,M,hM,hcenter,hScale⟩ :=
    SphericalPureDenominatorScaleLower.pure_partition_source_band_scale_lower_tail
      p (by omega) 1 (by positivity) h
  obtain ⟨C,hC,hComp⟩ := pure_cap_quantity_eventually_le_band_scale
    p hp h m M hM.le hcenter A K hA
  intro ε hε
  let ρ := ε/2
  have hρ : 0 < ρ := half_pos hε
  obtain ⟨L,δ,b,hL,hδ,hb,hLow⟩ := hScale ρ hρ
  let η := δ*Real.exp (-β*L)/C
  have hη : 0 < η := div_pos (mul_pos hδ (Real.exp_pos _)) hC
  refine ⟨η,hη,?_⟩
  let low (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | partition (n+3) β (field (mixtureCoefficients μ) J) < η*A n}
  let sourceLow (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
      δ*Real.exp (-β*L)*sourceCriticalBandScale (n+2) μ h.overlap_range β
        (m (n+1))}
  have hEventual : ∀ᶠ n : ℕ in atTop, low n ≤ sourceLow n := by
    filter_upwards [hComp] with n hn
    have hthreshold : η*A n ≤
        δ*Real.exp (-β*L)*sourceCriticalBandScale (n+2) μ
          h.overlap_range β (m (n+1)) := by
      calc
        _ ≤ η*(C*sourceCriticalBandScale (n+2) μ
            h.overlap_range β (m (n+1))) :=
          mul_le_mul_of_nonneg_left hn hη.le
        _ = _ := by
          dsimp [η]
          field_simp
    exact measureReal_mono (fun J hJ => lt_of_lt_of_le hJ hthreshold)
      (by finiteness)
  have hLowCob : IsCoboundedUnder (· ≤ ·) atTop low :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
  have hSourceB : IsBoundedUnder (· ≤ ·) atTop sourceLow :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hh := limsup_le_limsup hEventual hLowCob hSourceB
  have hfinal := hh.trans hLow
  simpa only [low,sourceLow,ρ,show 2*(ε/2)=ε by ring,μ] using hfinal

end
end SlowEquilibration.SphericalPureDenominatorFixedCapTransfer
