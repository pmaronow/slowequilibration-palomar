-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapFullLaplaceUniform
public import SlowEquilibration.SphericalPureCapWindowRawLaplace
public import SlowEquilibration.SourceGaussianWindowRatioBridge

/-! Source §9 `pc-laplace` ratios for the literal raw Palm conditional cap
mean and its fixed microscopic window, after exact critical-value centering. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapSourceRatios
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalPureCapTailScale SphericalPureCapIntegralDecomposition
open SphericalPureCapFullLaplaceUniform SphericalPureCapWindowRawLaplace
open SphericalPureLaplaceUniformLogCurvature SphericalPureCapSourceScalars
open SourceGaussianLaplaceRatio SourceGaussianWindowFraction
open SourceGaussianWindowRatioBridge PureStationarity SphericalModel
open scoped Topology
set_option autoImplicit false

/-- The source conditional mean of the full positive cap at dimension
`N=n+2` and centered ground-energy shift `t`. -/
def sourceCapMean (p : ℕ) (β ep cp a : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (latitudeNormalization (n+1)).toReal *
    (∫ z in a..1, rawDensity p (n+2) β
      ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) z)

/-- The same conditional mean restricted to the source microscopic interval
`[√Q−w/√N, √Q+w/√N]`. -/
def sourceWindowMean (p : ℕ) (β ep cp q w : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (latitudeNormalization (n+1)).toReal *
    (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
      rawDensity p (n+2) β
        ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) z)

private theorem capScale_pos (n : ℕ) (F r : ℝ) :
    0 < capScale (n+2) F r := by
  unfold capScale
  positivity

/-- The three source `pc-laplace` ratios hold uniformly over every fixed
energy-shift interval, for the same cap cutoff and literal Gaussian Γ(w).
The third quantity is the cap mass outside the microscopic window. -/
theorem sourcePure_cap_gaussian_ratios_uniform
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (L : ℝ) (hL : 0 ≤ L) :
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a b ε κ : ℝ,
      1/Real.sqrt 2 < a ∧ a < q-b ∧ 0 < b ∧ q+b < 1-ε ∧
      0 < ε ∧ ε < 1 ∧ 0 < κ ∧ κ = purePrintedKStar p hp β Q ∧
      pureResidualCoefficient p β a < 1/2 ∧ cp < β*a^p ∧
      ∀ w : ℝ, 0 < w →
        TendstoUniformlyOn
          (fun n t => sourceCapMean p β ep cp a n t /
            sourceCapMean p β ep cp a n 0)
          (fun t => Real.exp (β*t*q^p)) atTop (Icc (-L) L) ∧
        TendstoUniformlyOn
          (fun n t => sourceWindowMean p β ep cp q w n t /
            sourceCapMean p β ep cp a n 0)
          (fun t => Real.exp (β*t*q^p)*gaussianWindowFraction κ w)
          atTop (Icc (-L) L) ∧
        TendstoUniformlyOn
          (fun n t => (sourceCapMean p β ep cp a n t-
            sourceWindowMean p β ep cp q w n t) /
            sourceCapMean p β ep cp a n 0)
          (fun t => Real.exp (β*t*q^p)*(1-gaussianWindowFraction κ w))
          atTop (Icc (-L) L) := by
  dsimp only
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let F := CSParisiMeasure.variationalValue
    (FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)) β
  obtain ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,hTraw⟩ :=
    sourcePure_cap_full_laplace_uniform p hp h L hL
  refine ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,?_⟩
  obtain ⟨κw,hκw,hκwEq,hWraw⟩ := sourcePure_cap_raw_window_laplace_uniform p hp h
  have hκsame : κw = κ := hκwEq.trans hκEq.symm
  subst κw
  let J : ℝ := (1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)
  let G : ℝ := Real.sqrt (Real.pi/(κ/2))
  let C : ℝ := J*G
  let d : ℝ := β*q^p
  let T : ℕ → ℝ → ℝ := fun n t =>
    capScale (n+2) F (1/(2*x))*sourceCapMean p β ep cp a n t
  have hQ : 0 < 1-Q := sub_pos.mpr h.overlap_range.2
  have hJ : 0 < J := by
    dsimp [J]
    exact div_pos (Real.rpow_pos_of_pos hQ _) (by positivity)
  have hG : 0 < G := by dsimp [G]; positivity
  have hC : 0 < C := mul_pos hJ hG
  have hd : 0 ≤ d := by
    dsimp [d]
    exact mul_nonneg h.beta_pos.le (pow_nonneg (Real.sqrt_nonneg Q) _)
  intro w hw
  let W : ℕ → ℝ → ℝ := fun n t =>
    capScale (n+2) F (1/(2*x))*sourceWindowMean p β ep cp q w n t
  have hT : TendstoUniformlyOn T
      (fun t => C*Real.exp (d*t)) atTop (Icc (-L) L) := by
    convert hTraw using 1
    · funext n t
      rfl
    · funext t
      dsimp [C,J,G,d,q]
      ring
  have hW0 := hWraw L w hL hw.le
  rw [hκsame] at hW0
  have hW : TendstoUniformlyOn W
      (fun t => C*Real.exp (d*t)*gaussianWindowFraction κ w)
      atTop (Icc (-L) L) := by
    convert hW0 using 1
    · funext n t
      rfl
    · funext t
      dsimp [C,J,G,d,q]
      unfold gaussianWindowFraction
      field_simp
  have hΓ : 0 ≤ gaussianWindowFraction κ w :=
    (gaussianWindowFraction_pos hκ hw).le
  obtain ⟨hTr,hWr,hCr⟩ := uniform_cap_window_ratios hC hd hΓ hL hT hW
  have hcancelT (n : ℕ) (t : ℝ) :
      T n t/T n 0 =
        sourceCapMean p β ep cp a n t/sourceCapMean p β ep cp a n 0 := by
    dsimp [T]
    exact mul_div_mul_left _ _ (capScale_pos n F (1/(2*x))).ne'
  have hcancelW (n : ℕ) (t : ℝ) :
      W n t/T n 0 =
        sourceWindowMean p β ep cp q w n t/sourceCapMean p β ep cp a n 0 := by
    dsimp [T,W]
    exact mul_div_mul_left _ _ (capScale_pos n F (1/(2*x))).ne'
  have hcancelC (n : ℕ) (t : ℝ) :
      (T n t-W n t)/T n 0 =
        (sourceCapMean p β ep cp a n t-
          sourceWindowMean p β ep cp q w n t)/sourceCapMean p β ep cp a n 0 := by
    dsimp [T,W]
    rw [← mul_sub]
    exact mul_div_mul_left _ _ (capScale_pos n F (1/(2*x))).ne'
  have hcomm (t : ℝ) : d*t = β*t*q^p := by
    dsimp [d]
    ring
  refine ⟨?_,?_,?_⟩
  · simpa only [q,cp,ep,hcomm] using
      hTr.congr (Filter.Eventually.of_forall fun n t _ => hcancelT n t)
  · simpa only [q,cp,ep,hcomm] using
      hWr.congr (Filter.Eventually.of_forall fun n t _ => hcancelW n t)
  · simpa only [q,cp,ep,hcomm] using
      hCr.congr (Filter.Eventually.of_forall fun n t _ => hcancelC n t)

end
end SlowEquilibration.SphericalPureCapSourceRatios
