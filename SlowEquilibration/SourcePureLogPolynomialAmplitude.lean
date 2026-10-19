-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLogPolynomialEnvelope
public import SlowEquilibration.SourceGaussianLaplacePerturbed

/-! The exact logarithmic polynomial perturbation of the pure-model latitude
kernel, factored at the Gaussian contact latitude. -/
@[expose] public section
namespace SlowEquilibration.SourcePureLogPolynomialAmplitude
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

/-- The physical amplitude and logarithmic polynomial tilt after centering at
the contact latitude `m`. It is clipped to a fixed localization band. -/
def centeredAmplitude (a : ℝ → ℝ) (p : ℕ)
    (β cp m l r t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  if m+u/Real.sqrt (n+2 : ℕ) ∈ Icc l r then
    a (m+u/Real.sqrt (n+2 : ℕ)) *
      Real.exp (β*t*m^p + β*(t-Real.log (n+2 : ℕ)/(2*cp))*
        ((m+u/Real.sqrt (n+2 : ℕ))^p-m^p))
  else 0

/-- The amplitude is measurable for every dimension and parameter. -/
theorem measurable_centeredAmplitude {a : ℝ → ℝ} (ha : Measurable a)
    (p : ℕ) (β cp m l r t : ℝ) (n : ℕ) :
    Measurable (centeredAmplitude a p β cp m l r t n) := by
  unfold centeredAmplitude
  have hz : Measurable (fun u : ℝ => m+u/Real.sqrt (n+2 : ℕ)) := by fun_prop
  apply Measurable.ite (hz measurableSet_Icc)
  · fun_prop (disch := assumption)
  · exact measurable_const

/-- On every fixed microscopic displacement the source tilt disappears and
the amplitude tends to its exact contact value. -/
theorem centeredAmplitude_tendsto {a : ℝ → ℝ} {m l r : ℝ}
    (ha : ContinuousOn a (Icc l r))
    (hl : l < m) (hr : m < r) (hm : m ∈ Ioo (-1:ℝ) 1)
    (p : ℕ) (β cp t u : ℝ) :
    Tendsto (fun n : ℕ => centeredAmplitude a p β cp m l r t n u)
      atTop (𝓝 (a m * Real.exp (β*t*m^p))) := by
  let z : ℕ → ℝ := fun n => m+u/Real.sqrt (n+2 : ℕ)
  have hz := SourceGaussianLaplaceTaylor.scaled_tendsto m u
  have hevent : ∀ᶠ n : ℕ in atTop, z n ∈ Icc l r := by
    filter_upwards [hz.eventually (Ioo_mem_nhds hl hr)] with n hn
    exact ⟨hn.1.le,hn.2.le⟩
  have haLim : Tendsto (fun n => a (z n)) atTop (𝓝 (a m)) :=
    (ha.continuousAt (Icc_mem_nhds hl hr)).tendsto.comp hz
  have htilt := SourcePureLogPolynomialTangent.centered_log_polynomial_tendsto_zero
    p hm β t cp u
  have hexp : Tendsto (fun n : ℕ => Real.exp
      (β*t*m^p + β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z n^p-m^p)))
      atTop (𝓝 (Real.exp (β*t*m^p))) := by
    have hsum := (tendsto_const_nhds (x := β*t*m^p)).add htilt
    exact Real.continuous_exp.continuousAt.tendsto.comp (by
      convert hsum using 1; simp)
  have hraw := haLim.mul hexp
  exact hraw.congr' (by
    filter_upwards [hevent] with n hn
    simp only [centeredAmplitude, show m+u/Real.sqrt (n+2 : ℕ) ∈ Icc l r from hn,
      ↓reduceIte]
    rfl)

/-- A Gaussian envelope for the actual source logarithmic perturbation. The
allowable loss `δ` can be chosen below any strict quadratic saddle gap. -/
theorem exists_gaussian_bound {a : ℝ → ℝ} {m l r M : ℝ}
    (hM : 0 ≤ M) (hamp : ∀ z ∈ Icc l r, |a z| ≤ M)
    (hm : |m| ≤ 1) (hband : Icc l r ⊆ Icc (-1:ℝ) 1)
    (p : ℕ) (β cp t δ : ℝ) (hcp : 0 < cp) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n u,
      |centeredAmplitude a p β cp m l r t n u| ≤ B*Real.exp (δ*u^2) := by
  obtain ⟨K,hK,hKn⟩ := SourcePureLogPolynomialEnvelope.log_sqrt_uniform_bound
  let D : ℝ := |β| *(|t|+K/(2*cp))*(p:ℝ)
  let B : ℝ := M*Real.exp (|β*t*m^p|+D^2/(4*δ))
  refine ⟨B,mul_nonneg hM (Real.exp_pos _).le,?_⟩
  intro n u
  let z : ℝ := m+u/Real.sqrt (n+2 : ℕ)
  by_cases hz : z ∈ Icc l r
  · have htilt : |β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p)| ≤ D*|u| := by
      exact SourcePureLogPolynomialEnvelope.centered_polynomial_linear_bound
        p n m t u β cp K hcp (hKn n) hm
        ((abs_le.mpr ⟨(hband hz).1,(hband hz).2⟩))
    have hgauss : D*|u| ≤ δ*u^2+D^2/(4*δ) :=
      SourcePureLogPolynomialEnvelope.linear_gaussian_absorption hδ
    have hexp : Real.exp (β*t*m^p +
        β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p)) ≤
        Real.exp (|β*t*m^p|+D^2/(4*δ))*Real.exp (δ*u^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hbase := le_abs_self (β*t*m^p)
      have htilt' := le_abs_self
        (β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p))
      linarith
    change |centeredAmplitude a p β cp m l r t n u| ≤ B*Real.exp (δ*u^2)
    simp only [centeredAmplitude, show m+u/Real.sqrt (n+2 : ℕ) ∈ Icc l r from hz,
      ↓reduceIte, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |a z| * Real.exp (β*t*m^p +
        β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p)) ≤
        M*(Real.exp (|β*t*m^p|+D^2/(4*δ))*Real.exp (δ*u^2)) :=
          mul_le_mul (hamp z hz) hexp (Real.exp_pos _).le hM
      _ = B*Real.exp (δ*u^2) := by dsimp [B]; ring
  · have hnonneg : 0 ≤ B*Real.exp (δ*u^2) :=
      mul_nonneg (mul_nonneg hM (Real.exp_pos _).le) (Real.exp_pos _).le
    simpa only [centeredAmplitude,
      show m+u/Real.sqrt (n+2 : ℕ) ∉ Icc l r from hz,
      ↓reduceIte, abs_zero] using hnonneg

end
end SlowEquilibration.SourcePureLogPolynomialAmplitude
