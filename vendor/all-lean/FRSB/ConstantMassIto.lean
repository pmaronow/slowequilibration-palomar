module
public import FRSB.ConstantMassBackwardTest
public import Paper.ParisiStateShift
public import Paper.ItoExpectation

@[expose] public section

/-! Weighted backward identities for the actual selected Brownian state on
a constant-CDF interval. No supplied transition law or martingale premise is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper StochasticCalculus
open scoped Topology NNReal
namespace FRSB

/-- The capped test is a true martingale observable until every interior
endpoint of the constant-CDF interval. -/
theorem selectedParisiItoState_constantMass_weighted_interior
    (β h : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (a c : ℝ≥0) (b m : ℝ)
    (hab : (a : ℝ) < b) (hb : b ≤ 1) (hcend : (c : ℝ) < b - a)
    (hm : m ∈ Icc (0 : ℝ) 1)
    (hcdf : ∀ s ∈ Ico (a : ℝ) b, parisiCDF μ s = m)
    (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ) (L L1 : ℝ) (hL : 0 ≤ L) (hL1 : 0 ≤ L1)
    (hψb : ∀ x, |ψ x| ≤ L) (hψd : ∀ x, |deriv ψ x| ≤ L1)
    (Z : BrownianSample → ℝ) (hZ : StronglyMeasurable[canonicalBrownianFiltration a] Z)
    (C : ℝ≥0) (hC : ∀ sample : BrownianSample, ‖Z sample‖ ≤ C) :
    (∫ ω, Z ω * parisiBackwardQuotient β μ b m ψ (β ^ 2 * (b - a - c))
      (selectedParisiItoState β h hβ μ (a + c) ω) ∂canonicalBrownianMeasure) =
      ∫ ω, Z ω * parisiBackwardQuotient β μ b m ψ (β ^ 2 * (b - a))
        (selectedParisiItoState β h hβ μ a ω) ∂canonicalBrownianMeasure := by
  let v := fun t x => parisiGradient β μ (t, x)
  let hv := continuous_parisiGradient β μ
  let hvb := fun t x => norm_parisiGradient_le_one β μ (t, x)
  let hvl := lipschitzWith_parisiGradient β hβ μ
  let X := canonicalParisiShiftState β h μ v hv hvb hvl a
  let d := canonicalParisiShiftDrift β h μ v hv hvb hvl a
  let δ : ℝ := (b - a - c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hcap : (c : ℝ) + δ ≤ b - a := by dsimp [δ]; linarith
  have hbb : b ∈ Icc (0 : ℝ) 1 := ⟨a.coe_nonneg.trans hab.le, hb⟩
  have hD := heatC2Datum_exp_parisiPotential β μ b m hbb hm
  change HeatC2Datum (parisiHeatWeight β μ b m) at hD
  have hN := hD.mul hψ
  have hp := fun v x => (gaussianHeatFlow_parisiHeatWeight_pos β μ b m v x hbb).ne'
  let f := cappedBackwardHeatQuotient
    (fun y => parisiHeatWeight β μ b m y * ψ y) (parisiHeatWeight β μ b m) β (b - a) c δ
  obtain ⟨hf, hdt, hdx, hxx⟩ := cappedBackwardHeatQuotient_ito_continuous hN hD hp
    β (b - a) c δ hβ hδ hcap
  have hZ0 : StronglyMeasurable[canonicalBrownianShiftFiltration a 0] Z := by
    change StronglyMeasurable[canonicalBrownianFiltration (a + 0)] Z
    rw [add_zero]
    exact hZ
  have hvalue (r : ℝ≥0) : Integrable (fun ω => Z ω * f r (X r ω)) canonicalBrownianMeasure := by
    apply (integrable_const ((C : ℝ) * L)).mono'
    · exact ((hZ.mono (canonicalBrownianFiltration.le a)).mul
        (hf.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk
          ((stronglyAdapted_canonicalParisiShiftState β h μ v hv hvb hvl a r).mono
            ((canonicalBrownianShiftFiltration a).le r))))).aestronglyMeasurable
    · filter_upwards [] with ω
      rw [norm_mul]
      apply mul_le_mul (hC ω) _ (norm_nonneg _) C.coe_nonneg
      simpa only [f, cappedBackwardHeatQuotient, parisiBackwardQuotient, Real.norm_eq_abs] using
        abs_parisiBackwardQuotient_le β μ b m hbb hm ψ hψ L hψb
          (β ^ 2 * (b - a - hjbTimeCap c δ r)) (X r ω)
  have hK : ∀ s ∈ Icc (0 : ℝ) (c : ℝ), ∀ x,
      ‖itoSpaceDerivative f s x‖ ≤ (L1 + 2 * |m| * L).toNNReal := by
    intro s hs x
    rw [(cappedBackwardHeatQuotient_ito_derivatives hN hD hp β (b - a) c δ s x hβ hδ hcap).2.1]
    rw [Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)]
    exact abs_parisiBackwardQuotientDx_le β μ b m hbb hm ψ hψ L L1 hL hψb hψd _ x
  have hPDE : ∀ ω, ∀ s ∈ Icc (0 : ℝ) (c : ℝ),
      itoTimeDerivative f s (X s.toNNReal ω) +
        itoSpaceDerivative f s (X s.toNNReal ω) * d s.toNNReal ω +
          (1 / 2 : ℝ) * itoSpaceSecondDerivative f s (X s.toNNReal ω) * β ^ 2 = 0 := by
    intro ω s hs
    have hs1 : (a : ℝ) + s ≤ 1 := by linarith [hs.2]
    have hsm : parisiCDF μ ((a : ℝ) + s) = m :=
      hcdf _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hd : d s.toNNReal ω = β ^ 2 * m * parisiGradient β μ ((a : ℝ) + s, X s.toNNReal ω) := by
      change (if (((a + s.toNNReal : ℝ≥0) : ℝ)) ≤ 1 then
        β ^ 2 * parisiCDF μ ((a + s.toNNReal : ℝ≥0) : ℝ) *
          parisiGradient β μ (((a + s.toNNReal : ℝ≥0) : ℝ), X s.toNNReal ω) else 0) = _
      have htime : (((a + s.toNNReal : ℝ≥0) : ℝ)) = (a : ℝ) + s := by
        rw [NNReal.coe_add, Real.coe_toNNReal s hs.1]
      rw [htime]
      rw [ite_eq_left hs1, hsm]
    rw [hd]
    exact capped_parisiBackwardQuotient_PDE β hβ μ a.coe_nonneg hab hb hm hcdf ψ hψ
      c δ s (X s.toNNReal ω) hδ hcap hs.1 hs.2
  have he := backward_weighted_expectation_of_boundedDrift
    (boundedDriftItoCharacteristics_canonicalParisiShift β h μ v hv hvb hvl a)
    f hf
    (fun x s => (hasDerivAt_cappedBackwardHeatQuotient_time hN hD hp
      β (b - a) c δ s x hβ hδ hcap).differentiableAt)
    (fun s => contDiff_cappedBackwardHeatQuotient_spatial hN hD hp β (b - a) c δ s)
    hdt hdx hxx c _ hK Z hZ0 C hC hPDE (hvalue 0) (hvalue c)
  simpa only [f, X, canonicalParisiShiftState, v, hv, hvb, hvl,
    cappedBackwardHeatQuotient, hjbTimeCap_of_le c δ (c : ℝ) le_rfl,
    hjbTimeCap_of_le c δ 0 c.coe_nonneg, sub_zero, add_zero,
    parisiBackwardQuotient, selectedParisiItoState] using he

end FRSB
