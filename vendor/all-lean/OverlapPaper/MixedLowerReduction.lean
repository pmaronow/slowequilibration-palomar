module
public import OverlapPaper.MixedInterpolation
public import OverlapPaper.PhysicalParisiUpper
public import FourPapersCommon.MixedSchemeMinimizer

@[expose] public section

/-! An explicit reduction of the physical mixed lower bound.

The substantive interpolation-convergence input is stated separately here.
`OverlapPaper.MixedParisiFormula` discharges it using genuine constrained
mixed-model interpolation, including all signed-overlap endpoint cases.
-/
noncomputable section
open MeasureTheory ProbabilityTheory SpinGlass.Targets Filter Set
open scoped Topology
namespace OverlapPaper
open FourPapersCommon

theorem exists_scheme_mixedFunctional_lt (ξ : AdmissibleEvenMixture) (h ε : ℝ)
    (hε : 0 < ε) :
    ∃ (k : ℕ) (s : RSBScheme k),
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) < mixedPressure ξ h + ε := by
  have ht := ((continuous_mixedFunctional ξ h).tendsto (mixedMinimizer ξ h)).comp
    (FRSB.tendsto_parisiGridMeasure (mixedMinimizer ξ h))
  rw [mixedMinimizer_value] at ht
  have he := ht.eventually (eventually_lt_nhds (lt_add_of_pos_right (mixedPressure ξ h) hε))
  obtain ⟨n, hn⟩ := he.exists
  refine ⟨n + 1, Paper.parisiGridRSBScheme (mixedMinimizer ξ h) n, ?_⟩
  rw [FRSB.parisiSchemeMeasure_grid_eq]
  exact hn

theorem exists_nearOptimal_mixedScheme_minimizer (ξ : AdmissibleEvenMixture) (h ε : ℝ)
    (hε : 0 < ε) :
    ∃ (k : ℕ) (s : RSBScheme k),
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε ∧
      ∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedFunctional ξ h (Paper.parisiSchemeMeasure s') := by
  obtain ⟨k, s₀, hs₀⟩ := exists_scheme_mixedFunctional_lt ξ h ε hε
  obtain ⟨s, hs⟩ := exists_minimizer_mixedFunctional_scheme ξ k h
  exact ⟨k, s, (hs s₀).trans hs₀.le, hs⟩

/-- The exact near-optimal interpolation property used in the lower-bound
deduction. Its actual-model proof is `mixedNearOptimalInterpolation` in
`OverlapPaper.MixedParisiFormula`. -/
def MixedNearOptimalInterpolation (ξ : AdmissibleEvenMixture) (h : ℝ) : Prop :=
  ∀ {t₀ : ℝ}, t₀ < 1 →
    ∃ ε > (0 : ℝ), ∀ {k : ℕ} (s : RSBScheme k),
      mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤ mixedPressure ξ h + ε →
      (∀ s' : RSBScheme k, mixedFunctional ξ h (Paper.parisiSchemeMeasure s) ≤
        mixedFunctional ξ h (Paper.parisiSchemeMeasure s')) →
      ∀ t, 0 ≤ t → t ≤ t₀ →
        Tendsto (fun N => physicalMixedPhi ξ h s N t) atTop (𝓝 (mixedGuerraPsi ξ h s t))

theorem thermodynamicPressure_eq_mixedPressure_of_nearOptimalInterpolation
    (ξ : AdmissibleEvenMixture) (h : ℝ) (hlower : MixedNearOptimalInterpolation ξ h) :
    thermodynamicPressure ξ h = mixedPressure ξ h := by
  apply le_antisymm (thermodynamicPressure_le_mixedPressure ξ h)
  by_contra hn
  have hgap : 0 < mixedPressure ξ h - thermodynamicPressure ξ h := by
    exact sub_pos.mpr (lt_of_not_ge hn)
  let L := mixedGuerraDerivativeBound ξ
  have hL : 0 < L := mixedGuerraDerivativeBound_pos ξ
  let η := mixedPressure ξ h - thermodynamicPressure ξ h
  have hη : 0 < η := hgap
  let t₀ := max 0 (1 - η / (2 * (L + 1)))
  have ht₀0 : 0 ≤ t₀ := le_max_left _ _
  have ht₀1 : t₀ < 1 := by
    apply max_lt zero_lt_one
    have hh : 0 < η / (2 * (L + 1)) := by positivity
    linarith
  have hsmall : L * (1 - t₀) ≤ η / 2 := by
    have hh : 1 - t₀ ≤ η / (2 * (L + 1)) := by
      have hh := le_max_right (0 : ℝ) (1 - η / (2 * (L + 1)))
      change 1 - η / (2 * (L + 1)) ≤ t₀ at hh
      linarith
    have hf : L / (L + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ ≤ L * (η / (2 * (L + 1))) := mul_le_mul_of_nonneg_left hh hL.le
      _ = (η / 2) * (L / (L + 1)) := by field_simp
      _ ≤ η / 2 := mul_le_of_le_one_right (by positivity) hf
  obtain ⟨ε, hε, hc⟩ := hlower ht₀1
  obtain ⟨k, s, hs, hm⟩ := exists_nearOptimal_mixedScheme_minimizer ξ h ε hε
  have ht := hc s hs hm t₀ ht₀0 le_rfl
  have hle : mixedGuerraPsi ξ h s t₀ - L * (1 - t₀) ≤ thermodynamicPressure ξ h := by
    apply le_of_tendsto_of_tendsto (ht.sub_const (L * (1 - t₀)))
      (tendsto_expectedFreeEnergy ξ h)
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact physicalMixedPhi_endpoint_lower ξ hN h s ⟨ht₀0, ht₀1.le⟩
  have hp := mixedGuerraPsi_ge_pressure ξ h s ht₀1.le
  dsimp only [η] at hη hsmall
  linarith

theorem physicalParisi_formula_of_nearOptimalInterpolation (ξ : AdmissibleEvenMixture)
    (h : ℝ) (hlower : MixedNearOptimalInterpolation ξ h) :
    Tendsto (expectedFreeEnergy ξ h) atTop (𝓝 (mixedPressure ξ h)) := by
  rw [← thermodynamicPressure_eq_mixedPressure_of_nearOptimalInterpolation ξ h hlower]
  exact tendsto_expectedFreeEnergy ξ h

end OverlapPaper
