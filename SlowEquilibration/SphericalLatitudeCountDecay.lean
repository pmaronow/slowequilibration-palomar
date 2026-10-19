-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeHeightEnvelope

@[expose] public section

/-! Exponential exclusion of literal affine-latitude critical points in the
submaximal height window. Every density, determinant and scalar tail bound
is instantiated for the physical tensor field. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.StrongFieldComplexity
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_actual_count_halfNegative_decay (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    {ε : ℝ} (hε : 0 < ε) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)), ‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)), (∀ x, inner ℝ (e x) w=0) →
      (∫⁻ J, actualLatitudeSphereCount c w e q
        (fun J y => if latitudeField c J w e q y ∈
          Icc (((n+3 : ℕ) : ℝ)*(-Real.sqrt a/2)) (((n+3 : ℕ) : ℝ)*(Real.sqrt a-ε)) then 1 else 0) J
            ∂disorderLaw (n+3) μ.maxDegree) ≤
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let L := -Real.sqrt a/2
  let U := Real.sqrt a-ε
  obtain ⟨B,γ,κ,hB,hγ,hκ,henv⟩ := latitudeIntensity_halfNegative_envelope μ hQ hq0 hq1 hab hε
  let D := B*Real.sqrt (Real.pi/κ)*(|U-L|+1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hgauss : (∫⁻ k : ℝ, ENNReal.ofReal (Real.exp (-κ*k^2)))=
      ENNReal.ofReal (Real.sqrt (Real.pi/κ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hκ)
      (Filter.Eventually.of_forall (fun k => (Real.exp_pos _).le)), integral_gaussian]
  have hdim : ∀ᶠ n : ℕ in atTop, polynomialAbsorptionThreshold D 1 (γ/2) ≤ ((n+3 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (polynomialAbsorptionThreshold D 1 (γ/2)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (polynomialAbsorptionThreshold D 1 (γ/2)) ≤ n+3 by omega))
  refine ⟨γ/2, by positivity, ?_⟩
  filter_upwards [henv,hdim] with n hn hdim
  intro w hw e he
  rw [actual_latitude_height_count n μ hQ w hw e he hq0 hq1]
  have hN : 0 < ((n+3 : ℕ) : ℝ) := by positivity
  let T := ENNReal.ofReal (B*((n+3 : ℕ) : ℝ)*Real.exp (-γ*((n+3 : ℕ) : ℝ)))*
    ENNReal.ofReal (Real.sqrt (Real.pi/κ))
  have hpoint (h : ℝ) (hh : h ∈ Icc L U) :
      (∫⁻ k : ℝ, latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k])) ≤ T := by
    apply (lintegral_mono (fun k => hn h hh k)).trans_eq
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hgauss]
  have hbound : (∫⁻ h in Icc L U, ∫⁻ k : ℝ, latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k])) ≤
      ENNReal.ofReal (D*((n+3 : ℕ) : ℝ)*Real.exp (-γ*((n+3 : ℕ) : ℝ))) := by
    apply (setLIntegral_mono measurable_const hpoint).trans
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
    calc
      _ ≤ T*ENNReal.ofReal (|U-L|+1) :=
        by
          gcongr
          linarith [le_abs_self (U-L)]
      _ = _ := by
        dsimp only [T]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ B*((n+3 : ℕ) : ℝ)*Real.exp (-γ*((n+3 : ℕ) : ℝ))),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ (B*((n+3 : ℕ) : ℝ)*Real.exp (-γ*((n+3 : ℕ) : ℝ)))*Real.sqrt (Real.pi/κ))]
        congr 1
        dsimp only [D]
        ring
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  have hp := polynomial_le_exp_of_threshold 1 hD.le (show 0 < γ/2 by positivity) hdim
  simp only [pow_one] at hp
  calc
    _ ≤ Real.exp ((γ/2)*((n+3 : ℕ) : ℝ))*Real.exp (-γ*((n+3 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
