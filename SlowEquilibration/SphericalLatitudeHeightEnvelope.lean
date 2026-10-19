-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeIntensityBounds
public import SlowEquilibration.StrongFieldRadialTail

@[expose] public section

/-! A genuine exponentially small Gaussian envelope for the actual affine
critical intensity at all submaximal heights and every radial derivative. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.StrongFieldComplexity SlowEquilibration.GaussianCrudeDeterminant
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitudeIntensity_halfNegative_envelope (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    {ε : ℝ} (hε : 0 < ε) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    ∃ B γ κ : ℝ, 0 < B ∧ 0 < γ ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ h ∈ Icc (-Real.sqrt a/2) (Real.sqrt a-ε), ∀ k : ℝ,
        latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]) ≤
          ENNReal.ofReal (B*((n+3 : ℕ) : ℝ)*Real.exp (-γ*((n+3 : ℕ) : ℝ)))*
            ENNReal.ofReal (Real.exp (-κ*k^2)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  let v := latitudeConditionalValueVariance c q
  let C := (1-Real.log a)/2+crudeConstant b
  let A := a+b
  have ha : 0 < a := center_latitudeDerivativeVariance_pos μ hQ hq1
  have hb : 0 < b := center_latitudeCurvatureVariance_pos μ hQ hq1
  have hv : 0 < v := center_latitudeConditionalValueVariance_pos μ hQ hq0 hq1
  have hA : 0 < A := add_pos ha hb
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hheight : ∀ z ∈ heightBand a ε (-Real.sqrt a/2), |z.1| ≠ Real.sqrt a := by
    intro z hz heq
    rcases eq_or_eq_neg_of_abs_eq heq with heq | heq
    · have hu := hz.1.2; linarith
    · have hl := hz.1.1; linarith
  obtain ⟨γ,κ,hγ,hκ,henv⟩ := exists_exponential_envelope_closed hb hab hv
    (heightBand_isClosed a ε (-Real.sqrt a/2)) hheight
  obtain ⟨B1,hB1,hsharp⟩ := latitudePhysicalIntensity_eventually_compact_upper μ hQ hq0 hq1
  obtain ⟨B2,hB2,hcrude⟩ := latitudePhysicalIntensity_crude_upper μ hQ hq0 hq1
  let κt : ℝ := 1/(8*A)
  have hκt : 0 < κt := by dsimp only [κt]; positivity
  let Z := crudeRadialCutoff C A
  have hZ : 0 < Z := crudeRadialCutoff_pos C hA
  refine ⟨max B1 B2, min (γ/2) 1, min κ κt, lt_max_of_lt_left hB1,
    lt_min (by positivity) (by norm_num), lt_min hκ hκt, ?_⟩
  filter_upwards [hsharp hZ.le (show 0 < γ/2 by positivity)] with n hn
  intro h hh k
  have hN : 0 < ((n+3 : ℕ) : ℝ) := by positivity
  have hN1 : 1 ≤ ((n+3 : ℕ) : ℝ) := by norm_cast; omega
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ max B1 B2*((n+3 : ℕ) : ℝ)*
    Real.exp (-min (γ/2) 1*((n+3 : ℕ) : ℝ)))]
  by_cases hk : |k| ≤ Z
  · apply (hn h k hk).trans
    apply ENNReal.ofReal_le_ofReal
    have he := henv (h,k) ⟨hh, mem_univ k⟩
    have hpen : 0 ≤ κ*h^2 := by positivity
    have hsq : 0 ≤ κ*k^2 := by positivity
    have ht := mul_le_mul_of_nonneg_left he hN.le
    have hkeep := mul_le_mul_of_nonneg_right hN1 hsq
    have hc := mul_le_mul_of_nonneg_right (min_le_left (γ/2) 1) hN.le
    have hkappa := mul_le_mul_of_nonneg_right (min_le_left κ κt) (sq_nonneg k)
    have he' : ((n+3 : ℕ) : ℝ)*(exponent a b v h k+γ/2) ≤
        -min (γ/2) 1*((n+3 : ℕ) : ℝ)-min κ κt*k^2 := by
      change exponent a b v h k ≤ -γ-κ*(h^2+k^2) at he
      have hhN : 0 ≤ ((n+3 : ℕ) : ℝ)*(κ*h^2) := mul_nonneg hN.le hpen
      nlinarith
    calc
      _ ≤ (max B1 B2*((n+3 : ℕ) : ℝ))*Real.exp
          (-min (γ/2) 1*((n+3 : ℕ) : ℝ)-min κ κt*k^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left B1 B2) hN.le)
          (Real.exp_le_exp.mpr he') (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [show -min (γ/2) 1*((n+3 : ℕ) : ℝ)-min κ κt*k^2=
        -min (γ/2) 1*((n+3 : ℕ) : ℝ)+(-min κ κt*k^2) by ring, Real.exp_add]; ring
  · have hk' : Z ≤ |k| := (le_of_not_ge hk)
    apply (hcrude n h k).trans
    apply ENNReal.ofReal_le_ofReal
    have he := crudeRadial_exp_envelope C hA hv hN1 (a/A) h k hk'
    have hid : C+|k|-k^2/(2*A)-(h-a*k/A)^2/(2*v)=
        crudeRadialExponent C A v (a/A) h k := by unfold crudeRadialExponent; congr 2 <;> ring
    have he' : Real.exp (((n+3 : ℕ) : ℝ)*
        ((1-Real.log a)/2+crudeConstant b+|k|-k^2/(2*(a+b))-(h-a*k/(a+b))^2/(2*v))) ≤
          Real.exp (-((n+3 : ℕ) : ℝ))*Real.exp (-κt*k^2) := by
      change Real.exp (((n+3 : ℕ) : ℝ)*(C+|k|-k^2/(2*A)-(h-a*k/A)^2/(2*v))) ≤ _
      rw [hid]
      exact he
    have hcoeff : B2*((n+3 : ℕ) : ℝ) ≤ max B1 B2*((n+3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right B1 B2) hN.le
    have heg : Real.exp (-((n+3 : ℕ) : ℝ)) ≤ Real.exp (-min (γ/2) 1*((n+3 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (min_le_right (γ/2) 1) hN.le]
    have hek : Real.exp (-κt*k^2) ≤ Real.exp (-min κ κt*k^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (min_le_right κ κt) (sq_nonneg k)]
    calc
      _ ≤ (max B1 B2*((n+3 : ℕ) : ℝ))*(Real.exp (-((n+3 : ℕ) : ℝ))*Real.exp (-κt*k^2)) :=
        mul_le_mul hcoeff he' (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by
        have ht := mul_le_mul_of_nonneg_left
          (mul_le_mul heg hek (Real.exp_pos _).le (Real.exp_pos _).le)
            (show 0 ≤ max B1 B2*((n+3 : ℕ) : ℝ) by positivity)
        convert ht using 1 <;> ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
