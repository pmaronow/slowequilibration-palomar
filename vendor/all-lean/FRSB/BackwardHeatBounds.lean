module
public import FRSB.BackwardHeatData

@[expose] public section

/-! Uniform bounds for the actual backward Fourier quotient. These bounds
discharge the stochastic-integral and endpoint integrability requirements. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology ContDiff
namespace FRSB
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory

lemma integrable_gaussianHeatDatum {F : ℝ → ℝ} (hF : HeatC2Datum F) (v x : ℝ) :
    Integrable (fun z => F (x + z)) (gaussianReal 0 v.toNNReal) := by
  apply ((by simpa only [iteratedDeriv_zero] using hF.growth 0 (by norm_num) :
    HasExpGrowth F).comp_add_const x).integrable_gaussianReal
  exact (hF.smooth.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable

lemma abs_gaussianHeatFlow_le_of_relative {F D : ℝ → ℝ}
    (hF : HeatC2Datum F) (hD : HeatC2Datum D) (C v x : ℝ)
    (hrel : ∀ y, |F y| ≤ C * D y) :
    |gaussianHeatFlow F v x| ≤ C * gaussianHeatFlow D v x := by
  unfold gaussianHeatFlow
  calc
    _ ≤ ∫ z, |F (x + z)| ∂gaussianReal 0 v.toNNReal := abs_integral_le_integral_abs
    _ ≤ ∫ z, C * D (x + z) ∂gaussianReal 0 v.toNNReal :=
      integral_mono (integrable_gaussianHeatDatum hF v x).abs
        ((integrable_gaussianHeatDatum hD v x).const_mul C) (fun z => hrel _)
    _ = _ := integral_const_mul _ _

lemma heatC2Datum_first {F : ℝ → ℝ} (hF : HeatC2Datum F) :
    HasExpGrowth (deriv F) := by
  simpa only [iteratedDeriv_one] using hF.growth 1 (by norm_num)

lemma abs_gaussianHeatFlow_first_le_of_relative {F D : ℝ → ℝ}
    (hF : HeatC2Datum F) (hD : HeatC2Datum D) (C v x : ℝ)
    (hrel : ∀ y, |deriv F y| ≤ C * D y) :
    |gaussianHeatFlow (deriv F) v x| ≤ C * gaussianHeatFlow D v x := by
  have hi : Integrable (fun z => deriv F (x + z)) (gaussianReal 0 v.toNNReal) := by
    apply ((heatC2Datum_first hF).comp_add_const x).integrable_gaussianReal
    exact ((hF.smooth.continuous_deriv (by norm_num)).comp
      (continuous_const.add continuous_id)).aestronglyMeasurable
  unfold gaussianHeatFlow
  calc
    _ ≤ ∫ z, |deriv F (x + z)| ∂gaussianReal 0 v.toNNReal := abs_integral_le_integral_abs
    _ ≤ ∫ z, C * D (x + z) ∂gaussianReal 0 v.toNNReal :=
      integral_mono hi.abs ((integrable_gaussianHeatDatum hD v x).const_mul C)
        (fun z => hrel _)
    _ = _ := integral_const_mul _ _

theorem abs_backwardHeatQuotient_le {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D) (C v x : ℝ)
    (hp : 0 < gaussianHeatFlow D v x) (hrel : ∀ y, |N y| ≤ C * D y) :
    |backwardHeatQuotient N D v x| ≤ C := by
  rw [backwardHeatQuotient, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  exact abs_gaussianHeatFlow_le_of_relative hN hD C v x hrel

theorem abs_backwardHeatQuotientDx_le {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D) (C Cn Cd v x : ℝ)
    (hp : 0 < gaussianHeatFlow D v x) (hC : 0 ≤ C) (hCd : 0 ≤ Cd)
    (hrel : ∀ y, |N y| ≤ C * D y)
    (hn : ∀ y, |deriv N y| ≤ Cn * D y)
    (hd : ∀ y, |deriv D y| ≤ Cd * D y) :
    |backwardHeatQuotientDx N D v x| ≤ Cn + C * Cd := by
  have hn' : |gaussianHeatFlow (deriv N) v x / gaussianHeatFlow D v x| ≤ Cn := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact abs_gaussianHeatFlow_first_le_of_relative hN hD Cn v x hn
  have hd' : |gaussianHeatFlow (deriv D) v x / gaussianHeatFlow D v x| ≤ Cd := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact abs_gaussianHeatFlow_first_le_of_relative hD hD Cd v x hd
  have he : backwardHeatQuotientDx N D v x =
      gaussianHeatFlow (deriv N) v x / gaussianHeatFlow D v x -
        backwardHeatQuotient N D v x *
          (gaussianHeatFlow (deriv D) v x / gaussianHeatFlow D v x) := by
    unfold backwardHeatQuotientDx backwardHeatQuotient
    field_simp
  rw [he]
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  exact (hsub _ _).trans (add_le_add hn' (by
    rw [abs_mul]
    exact mul_le_mul (abs_backwardHeatQuotient_le hN hD C v x hp hrel) hd'
      (abs_nonneg _) hC))

def parisiHeatWeight (β : ℝ) (μ : ParisiMeasure) (b m x : ℝ) : ℝ :=
  Real.exp (m * parisiPotential β μ (b, x))

theorem gaussianHeatFlow_parisiHeatWeight_pos (β : ℝ) (μ : ParisiMeasure)
    (b m v x : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    0 < gaussianHeatFlow (parisiHeatWeight β μ b m) v x :=
  integral_exp_mul_comp_add_pos (parisiPotential_hasLinearGrowth β μ b hb)
    ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable
    m v.toNNReal x

theorem deriv_parisiHeatWeight (β : ℝ) (μ : ParisiMeasure) (b m x : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    deriv (parisiHeatWeight β μ b m) x =
      m * parisiGradient β μ (b, x) * parisiHeatWeight β μ b m x := by
  exact (((hasDerivAt_parisiPotential_spatial_all β μ b x hb).const_mul m).exp).deriv.trans
    (by dsimp [parisiHeatWeight]; ring)

theorem abs_deriv_parisiHeatWeight_le (β : ℝ) (μ : ParisiMeasure) (b m x : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    |deriv (parisiHeatWeight β μ b m) x| ≤ |m| * parisiHeatWeight β μ b m x := by
  rw [deriv_parisiHeatWeight β μ b m x hb, abs_mul, abs_mul,
    abs_of_pos (show 0 < parisiHeatWeight β μ b m x from Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg m)
      (by simpa only [Real.norm_eq_abs] using norm_parisiGradient_le_one β μ (b, x)))
    (Real.exp_pos _).le

theorem abs_parisiHeatWeight_mul_le (β : ℝ) (μ : ParisiMeasure) (b m : ℝ)
    (ψ : ℝ → ℝ) (L : ℝ) (hψ : ∀ x, |ψ x| ≤ L) (x : ℝ) :
    |parisiHeatWeight β μ b m x * ψ x| ≤ L * parisiHeatWeight β μ b m x := by
  rw [abs_mul, abs_of_pos (show 0 < parisiHeatWeight β μ b m x from Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hψ x) (Real.exp_pos _).le

theorem abs_deriv_parisiHeatWeight_mul_le (β : ℝ) (μ : ParisiMeasure) (b m : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (ψ : ℝ → ℝ) (hψ : HeatC2Datum ψ)
    (L L1 : ℝ) (hL : 0 ≤ L) (hψb : ∀ x, |ψ x| ≤ L)
    (hψd : ∀ x, |deriv ψ x| ≤ L1) (x : ℝ) :
    |deriv (fun y => parisiHeatWeight β μ b m y * ψ y) x| ≤
      (|m| * L + L1) * parisiHeatWeight β μ b m x := by
  have hweight : HasDerivAt (parisiHeatWeight β μ b m)
      (m * parisiGradient β μ (b, x) * parisiHeatWeight β μ b m x) x := by
    convert (((hasDerivAt_parisiPotential_spatial_all β μ b x hb).const_mul m).exp) using 1
    · rfl
    · dsimp [parisiHeatWeight]
      ring
  have hd := hweight.mul
    ((hψ.smooth.differentiable (by norm_num) x).hasDerivAt)
  change |deriv (parisiHeatWeight β μ b m * ψ) x| ≤ _
  rw [hd.deriv]
  change |(m * parisiGradient β μ (b, x) * parisiHeatWeight β μ b m x) * ψ x +
    parisiHeatWeight β μ b m x * deriv ψ x| ≤ _
  calc
    _ ≤ |(m * parisiGradient β μ (b, x) * parisiHeatWeight β μ b m x) * ψ x| +
      |parisiHeatWeight β μ b m x * deriv ψ x| := abs_add_le _ _
    _ ≤ (|m| * parisiHeatWeight β μ b m x) * L +
      parisiHeatWeight β μ b m x * L1 := by
      apply add_le_add
      · rw [abs_mul]
        have hh := abs_deriv_parisiHeatWeight_le β μ b m x hb
        rw [deriv_parisiHeatWeight β μ b m x hb] at hh
        exact mul_le_mul hh (hψb x) (abs_nonneg _)
          (mul_nonneg (abs_nonneg m) (Real.exp_pos _).le)
      · rw [abs_mul, abs_of_pos (show 0 < parisiHeatWeight β μ b m x from Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hψd x) (Real.exp_pos _).le
    _ = _ := by ring

end FRSB
