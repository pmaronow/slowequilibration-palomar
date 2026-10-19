module
public import FRSB.BackwardHeatTest
public import FRSB.ConstantMassTransform

@[expose] public section

/-! Actual constant-CDF backward tests, with the denominator identified
with exp(m*u). The pointwise PDE uses the selected potential and gradient. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper StochasticCalculus
open scoped Topology ContDiff NNReal
namespace FRSB
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory

def parisiBackwardQuotient (β : ℝ) (μ : ParisiMeasure) (b m : ℝ)
    (ψ : ℝ → ℝ) (v x : ℝ) : ℝ :=
  backwardHeatQuotient (fun y => parisiHeatWeight β μ b m y * ψ y)
    (parisiHeatWeight β μ b m) v x

theorem gaussianHeatFlow_parisiHeatWeight_on_constant_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {r : ℝ} (hr : r ∈ Icc a b) (x : ℝ) :
    gaussianHeatFlow (parisiHeatWeight β μ b m) (β ^ 2 * (b - r)) x =
      Real.exp (m * parisiPotential β μ (r, x)) := by
  by_cases hm : m = 0
  · simp [gaussianHeatFlow, parisiHeatWeight, hm]
  · rw [parisiPotential_coleHopf_constant_interval β hβ μ ha hab hb hc hr
      (show b ∈ Icc r b from ⟨hr.2, le_rfl⟩) x,
      exp_mul_coleHopf (parisiPotential_hasLinearGrowth β μ b ⟨ha.trans hab.le, hb⟩)
        ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable hm]
    rfl

theorem gaussianHeatFlow_parisiHeatWeight_log_gradient (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hm : m ∈ Icc (0 : ℝ) 1) (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m)
    {r : ℝ} (hr : r ∈ Icc a b) (x : ℝ) :
    gaussianHeatFlow (deriv (parisiHeatWeight β μ b m)) (β ^ 2 * (b - r)) x /
      gaussianHeatFlow (parisiHeatWeight β μ b m) (β ^ 2 * (b - r)) x =
        m * parisiGradient β μ (r, x) := by
  have hd := hasDerivAt_gaussianHeatFlow_spatial
    (heatC2Datum_exp_parisiPotential β μ b m ⟨ha.trans hab.le, hb⟩ hm)
    (β ^ 2 * (b - r)) x
  change HasDerivAt (gaussianHeatFlow (parisiHeatWeight β μ b m) (β ^ 2 * (b - r)))
    (gaussianHeatFlow (deriv (parisiHeatWeight β μ b m)) (β ^ 2 * (b - r)) x) x at hd
  have he : gaussianHeatFlow (parisiHeatWeight β μ b m) (β ^ 2 * (b - r)) =
      fun y => Real.exp (m * parisiPotential β μ (r, y)) := by
    funext y
    exact gaussianHeatFlow_parisiHeatWeight_on_constant_interval β hβ μ ha hab hb hc hr y
  rw [he] at hd
  have hd' := ((hasDerivAt_parisiPotential_spatial_all β μ r x ⟨ha.trans hr.1, hr.2.trans hb⟩).const_mul m).exp
  have hderiv := hd.unique hd'
  rw [hderiv, gaussianHeatFlow_parisiHeatWeight_on_constant_interval β hβ μ ha hab hb hc hr x]
  field_simp

theorem abs_parisiBackwardQuotient_le (β : ℝ) (μ : ParisiMeasure) (b m : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ) (L : ℝ) (hψb : ∀ y, |ψ y| ≤ L) (v x : ℝ) :
    |parisiBackwardQuotient β μ b m ψ v x| ≤ L :=
  abs_backwardHeatQuotient_le
    ((heatC2Datum_exp_parisiPotential β μ b m hb hm).mul hψ)
    (heatC2Datum_exp_parisiPotential β μ b m hb hm) L v x
    (gaussianHeatFlow_parisiHeatWeight_pos β μ b m v x hb)
    (abs_parisiHeatWeight_mul_le β μ b m ψ L hψb)

theorem abs_parisiBackwardQuotientDx_le (β : ℝ) (μ : ParisiMeasure) (b m : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hm : m ∈ Icc (0 : ℝ) 1)
    (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ) (L L1 : ℝ) (hL : 0 ≤ L)
    (hψb : ∀ y, |ψ y| ≤ L) (hψd : ∀ y, |deriv ψ y| ≤ L1) (v x : ℝ) :
    |backwardHeatQuotientDx (fun y => parisiHeatWeight β μ b m y * ψ y)
      (parisiHeatWeight β μ b m) v x| ≤ L1 + 2 * |m| * L := by
  have hh := abs_backwardHeatQuotientDx_le
    ((heatC2Datum_exp_parisiPotential β μ b m hb hm).mul hψ)
    (heatC2Datum_exp_parisiPotential β μ b m hb hm) L (|m| * L + L1) |m| v x
    (gaussianHeatFlow_parisiHeatWeight_pos β μ b m v x hb) hL (abs_nonneg m)
    (abs_parisiHeatWeight_mul_le β μ b m ψ L hψb)
    (abs_deriv_parisiHeatWeight_mul_le β μ b m hb ψ hψ L L1 hL hψb hψd)
    (fun y => abs_deriv_parisiHeatWeight_le β μ b m y hb)
  change |backwardHeatQuotientDx (fun y => Real.exp (m * parisiPotential β μ (b, y)) * ψ y)
    (fun y => Real.exp (m * parisiPotential β μ (b, y))) v x| ≤ _
  convert hh using 1 <;> ring

theorem parisiBackwardQuotient_terminal (β : ℝ) (μ : ParisiMeasure) (b m x : ℝ)
    (ψ : ℝ → ℝ) : parisiBackwardQuotient β μ b m ψ 0 x = ψ x := by
  simp [parisiBackwardQuotient, backwardHeatQuotient, gaussianHeatFlow,
    parisiHeatWeight, (Real.exp_pos _).ne']

/-- Genuine backward PDE on the constant-CDF cell, for a capped test which
agrees with the physical time on the stochastic interval. -/
theorem capped_parisiBackwardQuotient_PDE (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hm : m ∈ Icc (0 : ℝ) 1) (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m)
    (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ) (c δ s x : ℝ)
    (hδ : 0 < δ) (hcap : c + δ ≤ b - a) (hs : 0 ≤ s) (hsc : s ≤ c) :
    let f := cappedBackwardHeatQuotient
      (fun y => parisiHeatWeight β μ b m y * ψ y) (parisiHeatWeight β μ b m) β (b - a) c δ
    itoTimeDerivative f s x + itoSpaceDerivative f s x *
      (β ^ 2 * m * parisiGradient β μ (a + s, x)) +
        (1 / 2 : ℝ) * itoSpaceSecondDerivative f s x * β ^ 2 = 0 := by
  have hbb : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab.le, hb⟩
  have hD := heatC2Datum_exp_parisiPotential β μ b m hbb hm
  change HeatC2Datum (parisiHeatWeight β μ b m) at hD
  have hN := hD.mul hψ
  have hp := fun v x => (gaussianHeatFlow_parisiHeatWeight_pos β μ b m v x hbb).ne'
  dsimp only
  obtain ⟨hdt, hdx, hxx⟩ := cappedBackwardHeatQuotient_ito_derivatives hN hD hp
    β (b - a) c δ s x hβ hδ hcap
  rw [hdt, hdx, hxx, hjbTimeCap_of_le c δ s hsc]
  have hcapD : hjbTimeCapD c δ s = 1 := by simp [hjbTimeCapD, hsc]
  rw [hcapD]
  have hv : β ^ 2 * (b - a - s) = β ^ 2 * (b - (a + s)) := by ring
  rw [hv]
  have hh := backwardHeatQuotient_heat_generator
    (fun y => parisiHeatWeight β μ b m y * ψ y) (parisiHeatWeight β μ b m)
    (β ^ 2 * (b - (a + s))) x (hp _ _)
  rw [gaussianHeatFlow_parisiHeatWeight_log_gradient β hβ μ ha hab hb hm hc
    (show a + s ∈ Icc a b from ⟨by linarith, by linarith⟩) x] at hh
  convert congrArg (fun z : ℝ => β ^ 2 * z) hh using 1 <;> ring

end FRSB
