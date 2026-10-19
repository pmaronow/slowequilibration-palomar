-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeIntensityBounds
public import SlowEquilibration.SphericalLatitudePhysicalIntensity
public import SlowEquilibration.StrongFieldRadialLocalization
public import SlowEquilibration.StrongFieldLaplace

@[expose] public section

/-! # Exponential exclusion of actual off-endpoint latitude critical scores -/
namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter Classical
open SphericalModel SphericalGaussianJet StrongFieldComplexity SphericalMarkedWindows
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal compact radial window away from the positive endpoint. -/
def radialExcludedWindow (a b Z δ : ℝ) : Set ℝ :=
  Icc (-Z) Z ∩ {k | δ ≤ |k-radialEndpoint a b|}

lemma radialExcludedWindow_measurable (a b Z δ : ℝ) :
    MeasurableSet (radialExcludedWindow a b Z δ) :=
  measurableSet_Icc.inter (measurableSet_le measurable_const (measurable_id.sub_const _).abs)

theorem latitude_offEndpoint_count_exponential (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    (H : ℝ) {Z δ : ℝ} (hZ : 0 ≤ Z) (hδ : 0 < δ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    let b := latitudeCurvatureVariance c q
    ∃ η : ℝ,0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ x,inner ℝ (e x) w=0) →
      (∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => if actualLatitudeScore c w e q J y ∈
          rectangularScoreWindow (Icc 0 H) (radialExcludedWindow a b Z δ) then 1 else 0) J
            ∂disorderLaw (n+3) μ.maxDegree) ≤
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let a := latitudeDerivativeVariance c q
  let b := latitudeCurvatureVariance c q
  let v := latitudeConditionalValueVariance c q
  let U := radialExcludedWindow a b Z δ
  have hb : 0 < b := center_latitudeCurvatureVariance_pos μ hQ hq1
  have hv : 0 < v := center_latitudeConditionalValueVariance_pos μ hQ hq0 hq1
  obtain ⟨γ,hγ,hgap⟩ := exists_compact_positive_radial_gap hb hab hv H Z hδ
  obtain ⟨B,hB,hupper⟩ := latitudePhysicalIntensity_eventually_compact_upper μ hQ hq0 hq1
  let D := B*(|H|+1)*(2*Z+1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hdim : ∀ᶠ n : ℕ in atTop,polynomialAbsorptionThreshold D 1 (γ/4) ≤ ((n+3 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (polynomialAbsorptionThreshold D 1 (γ/4)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (polynomialAbsorptionThreshold D 1 (γ/4)) ≤ n+3 by omega))
  refine ⟨γ/4,by positivity,?_⟩
  filter_upwards [hupper hZ (by positivity : 0 < γ/2),hdim] with n hn hdim
  intro w hw e he
  rw [actual_latitude_rectangular_count n μ hQ w hw e he hq0 hq1
    (Icc 0 H) U measurableSet_Icc (radialExcludedWindow_measurable a b Z δ)]
  let T := ENNReal.ofReal (B*((n+3 : ℕ) : ℝ)*Real.exp (-(γ/2)*((n+3 : ℕ) : ℝ)))
  have hpoint (h : ℝ) (hh : h ∈ Icc 0 H) (k : ℝ) (hk : k ∈ U) :
      latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k]) ≤ T := by
    have hrad : k ∈ Icc (-Z) Z ∧ δ ≤ |k-radialEndpoint a b| := hk
    have hnorm : |k| ≤ Z := abs_le.mpr hrad.1
    apply (hn h k hnorm).trans
    apply ENNReal.ofReal_le_ofReal
    change B*((n+3 : ℕ) : ℝ)*Real.exp (((n+3 : ℕ) : ℝ)*(exponent a b v h k+γ/2)) ≤
      B*((n+3 : ℕ) : ℝ)*Real.exp (-(γ/2)*((n+3 : ℕ) : ℝ))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hg : exponent a b v h k ≤ -γ := hgap h hh k hrad.1 hrad.2
    have hm := mul_le_mul_of_nonneg_right hg (show (0:ℝ) ≤ ((n+3 : ℕ) : ℝ) from Nat.cast_nonneg _)
    nlinarith
  have hvolU : volume U ≤ ENNReal.ofReal (2*Z+1) := by
    apply (measure_mono (show U ⊆ Icc (-Z) Z from inter_subset_left)).trans
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hint (h : ℝ) (hh : h ∈ Icc 0 H) :
      (∫⁻ k in U,latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k])) ≤
        T*ENNReal.ofReal (2*Z+1) := by
    apply (setLIntegral_mono measurable_const (hpoint h hh)).trans
    rw [lintegral_const,Measure.restrict_apply_univ]
    simpa only [mul_comm] using mul_le_mul_left hvolU T
  have hbound : (∫⁻ h in Icc 0 H,∫⁻ k in U,latitudePhysicalIntensity n c q (WithLp.toLp 2 ![h,k])) ≤
      ENNReal.ofReal (D*((n+3 : ℕ) : ℝ)*Real.exp (-(γ/2)*((n+3 : ℕ) : ℝ))) := by
    apply (setLIntegral_mono measurable_const hint).trans
    rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
    calc
      _ ≤ T*ENNReal.ofReal (2*Z+1)*ENNReal.ofReal (|H|+1) := by
        gcongr
        linarith [le_abs_self H]
      _ = _ := by
        dsimp only [T]
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp only [D]
        ring
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  have hp := polynomial_le_exp_of_threshold 1 hD.le (show 0 < γ/4 by positivity) hdim
  simp only [pow_one] at hp
  calc
    _ ≤ Real.exp ((γ/4)*((n+3 : ℕ) : ℝ))*Real.exp (-(γ/2)*((n+3 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add];congr 1;ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
