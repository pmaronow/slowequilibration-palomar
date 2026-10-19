-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeIntensityBounds
public import SlowEquilibration.StrongFieldLaplace

@[expose] public section

/-! Genuine subexponential critical counts on every compact score window
in the strict strong-field regime. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.StrongFieldComplexity SlowEquilibration.SphericalMarkedWindows
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_actual_compact_count_subexponential (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    (L U K Z : ℝ) {ε : ℝ} (hε : 0<ε) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ x,inner ℝ (e x) w=0) →
      (∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => if actualLatitudeScore c w e q J y ∈
          rectangularScoreWindow (Icc L U) (Icc K Z) then 1 else 0) J
            ∂disorderLaw (n+3) μ.maxDegree)≤ENNReal.ofReal (Real.exp (ε*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  let v := latitudeConditionalValueVariance c q
  have hb : 0<b := center_latitudeCurvatureVariance_pos μ hQ hq1
  have hv : 0<v := center_latitudeConditionalValueVariance_pos μ hQ hq0 hq1
  obtain ⟨B,hB,hbound⟩ := latitudePhysicalIntensity_eventually_compact_upper μ hQ hq0 hq1
  let R := |K|+|Z|
  have hR : 0≤R := by dsimp [R]; positivity
  let D := B*(|U-L|+1)*(|Z-K|+1)
  have hD : 0<D := by dsimp [D]; positivity
  have hdim : ∀ᶠ n : ℕ in atTop,polynomialAbsorptionThreshold D 1 (ε/2)≤((n+3 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (polynomialAbsorptionThreshold D 1 (ε/2)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (polynomialAbsorptionThreshold D 1 (ε/2))≤n+3 by omega))
  filter_upwards [hbound hR (show 0<ε/2 by positivity),hdim] with n hn hdim
  intro w hw e he
  rw [actual_latitude_rectangular_count n μ hQ w hw e he hq0 hq1 _ _ measurableSet_Icc measurableSet_Icc]
  let T := ENNReal.ofReal (B*((n+3 : ℕ) : ℝ)*Real.exp (((n+3 : ℕ) : ℝ)*(ε/2)))
  have hpoint (h k : ℝ) (hk : k∈Icc K Z) :
      latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k])≤T := by
    have hkR : |k|≤R := by
      apply abs_le.mpr
      constructor
      · have hK := neg_abs_le K
        have hZ := abs_nonneg Z
        dsimp [R]
        linarith [hk.1]
      · have hZ := le_abs_self Z
        have hK := abs_nonneg K
        dsimp [R]
        linarith [hk.2]
    apply (hn h k hkR).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hex := exponent_nonpos_global hb hab hv h k
    have hN : 0≤((n+3 : ℕ) : ℝ) := by positivity
    nlinarith
  have hinner (h : ℝ) :
      (∫⁻ k in Icc K Z,latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]))≤
      T*ENNReal.ofReal (|Z-K|+1) := by
    apply (setLIntegral_mono measurable_const (fun k hk => hpoint h k hk)).trans
    rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
    gcongr
    linarith [le_abs_self (Z-K)]
  have htot : (∫⁻ h in Icc L U,∫⁻ k in Icc K Z,latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]))≤
      ENNReal.ofReal (D*((n+3 : ℕ) : ℝ)*Real.exp (((n+3 : ℕ) : ℝ)*(ε/2))) := by
    apply (setLIntegral_mono measurable_const (fun h _ => hinner h)).trans
    rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
    calc
      _ ≤ T*ENNReal.ofReal (|Z-K|+1)*ENNReal.ofReal (|U-L|+1) := by
        gcongr
        linarith [le_abs_self (U-L)]
      _ = _ := by
        dsimp only [T]
        rw [← ENNReal.ofReal_mul (by positivity : 0≤B*((n+3 : ℕ) : ℝ)*Real.exp (((n+3 : ℕ) : ℝ)*(ε/2))),
          ← ENNReal.ofReal_mul (by positivity : 0≤B*((n+3 : ℕ) : ℝ)*Real.exp (((n+3 : ℕ) : ℝ)*(ε/2))*(|Z-K|+1))]
        congr 1
        dsimp [D]
        ring
  apply htot.trans
  apply ENNReal.ofReal_le_ofReal
  have hp := polynomial_le_exp_of_threshold 1 hD.le (show 0<ε/2 by positivity) hdim
  simp only [pow_one] at hp
  calc
    _ ≤ Real.exp ((ε/2)*((n+3 : ℕ) : ℝ))*Real.exp (((n+3 : ℕ) : ℝ)*(ε/2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
