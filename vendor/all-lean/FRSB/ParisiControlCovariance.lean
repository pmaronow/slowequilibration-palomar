module
public import FRSB.ParisiConvexEquality
public import Paper.ParisiGradientMartingaleLaw

@[expose] public section

/-! Actual optimal-control covariance and the deterministic zero kernel forced
by equality of terminal drifts. Weighted expectations and Fubini are supplied
by the already checked Brownian/PDE construction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace FRSB
open Paper

lemma selectedParisiFeedbackControl_eq_process (β h : ℝ) (hβ : β ≠ 0)
    (ρ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    selectedParisiFeedbackControl β h ρ s =
      selectedParisiGradientProcess β h hβ ρ s.toNNReal := by
  funext ω
  rw [selectedParisiFeedbackControl_apply β h hβ ρ s hs ω]
  unfold selectedParisiGradientProcess
  rw [selectedParisiItoState_eq β h hβ ρ
    (by simpa only [Real.coe_toNNReal s hs.1] using hs.2), Real.coe_toNNReal s hs.1]

lemma selectedParisiFeedbackControl_terminal_weighted
    (β h : ℝ) (hβ : β ≠ 0) (ρ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (Z : BrownianSample → ℝ)
    (hZ : StronglyMeasurable[canonicalBrownianFiltration s.toNNReal] Z)
    (hb : ∀ ω, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * selectedParisiFeedbackControl β h ρ 1 ω ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * selectedParisiFeedbackControl β h ρ s ω ∂canonicalBrownianMeasure := by
  have hh := selectedParisiGradient_terminal_weighted_expectation β h hβ ρ s.toNNReal
    (by simpa only [Real.coe_toNNReal s hs.1] using hs.2) Z hZ hb
  rw [selectedParisiFeedbackControl_eq_process β h hβ ρ 1 (by norm_num),
    selectedParisiFeedbackControl_eq_process β h hβ ρ s hs]
  simpa only [Real.toNNReal_one, NNReal.coe_one, selectedParisiGradientProcess,
    Real.coe_toNNReal s hs.1] using hh

/-- The genuine martingale covariance equals its earlier second moment. -/
theorem selectedParisiFeedbackControl_covariance (β h : ℝ) (hβ : β ≠ 0)
    (ρ : ParisiMeasure) (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ ω, selectedParisiFeedbackControl β h ρ s ω *
      selectedParisiFeedbackControl β h ρ t ω ∂canonicalBrownianMeasure) =
      selectedParisiSecondMoment β h hβ ρ (min s t) := by
  let A := selectedParisiFeedbackControl β h ρ
  have hA : IsParisiAdmissibleControl A :=
    isParisiAdmissibleControl_selectedParisiFeedbackControl β h ρ
  have hstep (r u : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (hru : r ≤ u) :
      (∫ ω, A r ω * A u ω ∂canonicalBrownianMeasure) =
        selectedParisiSecondMoment β h hβ ρ r := by
    have hZr : StronglyMeasurable[canonicalBrownianFiltration r.toNNReal] (A r) := by
      have hh := hA.adapted r.toNNReal
      dsimp only at hh
      rw [Real.coe_toNNReal r hr.1] at hh
      exact hh
    have hZu : StronglyMeasurable[canonicalBrownianFiltration u.toNNReal] (A r) :=
      hZr.mono (canonicalBrownianFiltration.mono (Real.toNNReal_le_toNNReal hru))
    have hh := (selectedParisiFeedbackControl_terminal_weighted β h hβ ρ u hu
      (A r) hZu (hA.bounded r)).symm.trans
      (selectedParisiFeedbackControl_terminal_weighted β h hβ ρ r hr (A r) hZr (hA.bounded r))
    calc
      _ = ∫ ω, A r ω ^ 2 ∂canonicalBrownianMeasure := by
        simpa only [A, ← pow_two] using hh
      _ = _ := selectedParisiFeedbackControl_secondMoment_eq β h hβ ρ r hr
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact hstep s t hs ht hst
  · rw [min_eq_right hts]
    calc
      _ = ∫ ω, A t ω * A s ω ∂canonicalBrownianMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => mul_comm _ _
      _ = _ := hstep t s ht hs hts

/-- Equality of the two actual terminal drifts forces a zero moment kernel. -/
theorem selectedParisi_cdfKernel_zero_of_drift_ae_eq
    (β h : ℝ) (hβ : β ≠ 0) (ρ μ ν : ParisiMeasure)
    (hd : parisiControlDrift β μ (selectedParisiFeedbackControl β h ρ) =ᵐ[canonicalBrownianMeasure]
      parisiControlDrift β ν (selectedParisiFeedbackControl β h ρ)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..1, (parisiCDF μ s - parisiCDF ν s) *
        selectedParisiSecondMoment β h hβ ρ (min s t)) = 0 := by
  let A := selectedParisiFeedbackControl β h ρ
  let c := fun s => parisiCDF μ s - parisiCDF ν s
  have hA : IsParisiAdmissibleControl A :=
    isParisiAdmissibleControl_selectedParisiFeedbackControl β h ρ
  have hAm : ∀ ω, Measurable (fun s => A s ω) := fun ω =>
    hA.measurable.comp (f := fun s => (s, ω)) (measurable_id.prodMk measurable_const)
  have hc : Measurable c := (parisiCDF_measurable μ).sub (parisiCDF_measurable ν)
  have hcb : ∀ s, ‖c s‖ ≤ 1 := norm_parisiCDF_sub_le_one μ ν
  have hz : (fun ω => ∫ s in (0 : ℝ)..1, c s * A s ω) =ᵐ[canonicalBrownianMeasure] 0 := by
    filter_upwards [hd] with ω hω
    have hi := (parisiControl_intervalIntegrable μ A hAm hA.bounded ω).1
    have hj := (parisiControl_intervalIntegrable ν A hAm hA.bounded ω).1
    have he : (∫ s in (0 : ℝ)..1, c s * A s ω) =
        (∫ s in (0 : ℝ)..1, parisiCDF μ s * A s ω) -
          ∫ s in (0 : ℝ)..1, parisiCDF ν s * A s ω := by
      rw [← intervalIntegral.integral_sub hi hj]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only [c]
      ring
    rw [he]
    dsimp only [parisiControlDrift] at hω
    exact sub_eq_zero.mpr (mul_left_cancel₀ (pow_ne_zero 2 hβ) hω)
  intro t ht
  have hmt : Measurable (A t) :=
    hA.measurable.comp (f := fun ω => (t, ω)) (measurable_const.prodMk measurable_id)
  have hh := integral_weighted_control_intervalIntegral canonicalBrownianMeasure c hc hcb
    A hA.measurable hA.bounded (A t) hmt (hA.bounded t)
  have hleft : (∫ ω, A t ω * (∫ s in (0 : ℝ)..1, c s * A s ω) ∂canonicalBrownianMeasure) = 0 := by
    calc
      _ = ∫ ω : BrownianSample, (0 : ℝ) ∂canonicalBrownianMeasure := by
        apply integral_congr_ae
        filter_upwards [hz] with ω hω
        simp only [hω, Pi.zero_apply, mul_zero]
      _ = 0 := by simp
  rw [hleft] at hh
  apply Eq.trans ?_ hh.symm
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  have he := selectedParisiFeedbackControl_covariance β h hβ ρ t s ht hs
  rw [min_comm t s] at he
  exact congrArg (fun z => c s * z) he.symm

end FRSB
