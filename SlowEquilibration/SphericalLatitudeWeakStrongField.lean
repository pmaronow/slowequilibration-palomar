-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeStrongFieldMaximum
public import SlowEquilibration.SphericalLatitudeRegularDisorder

@[expose] public section

/-! Boundary extension of the actual strong-field maximum lower bound.
The center scale is held fixed while the positive affine latitude is moved
slightly outward; this decreases b/a strictly. The fields are coupled by
the same actual tensor and the proved regular-disorder continuity bound. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem center_latitude_strong_of_gt (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q r : ℝ} (hq0 : 0 ≤ q) (hqr : q < r) (hr1 : r < 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q ≤
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q) :
    latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) r <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) r := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hS : 0 < secondCovariance c 1 := by
    dsimp only [c]
    rw [secondCovariance_center, secondCovariance_mixture]
    exact mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have htq : 0 < 1-q^2 := by nlinarith
  have htr : 0 < 1-r^2 := by nlinarith
  have hsqr : q^2 < r^2 := (sq_lt_sq₀ hq0 (hq0.trans hqr.le)).mpr hqr
  have hbase : (1-q^2)*secondCovariance c 1 ≤ firstCovariance c 1 := by
    apply (mul_le_mul_iff_right₀ htq).mp
    convert hab using 1 <;> simp only [latitudeCurvatureVariance, latitudeDerivativeVariance] <;> ring
  have hstrict : (1-r^2)*secondCovariance c 1 < firstCovariance c 1 := by
    nlinarith [mul_pos (sub_pos.mpr hsqr) hS]
  have hh := mul_lt_mul_of_pos_left hstrict htr
  convert hh using 1 <;> simp only [latitudeCurvatureVariance, latitudeDerivativeVariance] <;> ring

theorem exists_strong_latitude_approximation (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q ≤
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    {ε : ℝ} (hε : 0 < ε) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∃ r ∈ Ioo q 1,
      latitudeCurvatureVariance c r < latitudeDerivativeVariance c r ∧
      Real.sqrt (latitudeDerivativeVariance c q)-ε/2 <
        Real.sqrt (latitudeDerivativeVariance c r)-2*derivativeConstant c*Real.sqrt |q-r| := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let F : ℝ → ℝ := fun r => Real.sqrt (latitudeDerivativeVariance c r)-
    2*derivativeConstant c*Real.sqrt |q-r|
  have hF : Continuous F := by unfold F latitudeDerivativeVariance; fun_prop
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hF.continuousAt (x := q)) (ε/2) (by positivity)
  let d := min (δ/2) ((1-q)/2)
  have hd : 0 < d := lt_min (by positivity) (by linarith [hq.2])
  have hdδ : d < δ := (min_le_left _ _).trans_lt (by linarith)
  have hd1 : d < 1-q := (min_le_right _ _).trans_lt (by linarith [hq.2])
  let r := q+d
  have hqr : q < r := by dsimp only [r]; linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hdist : dist r q < δ := by rw [Real.dist_eq, show r-q=d by dsimp only [r]; ring, abs_of_pos hd]; exact hdδ
  have hfq : F q=Real.sqrt (latitudeDerivativeVariance c q) := by simp [F]
  have hh := hclose hdist
  rw [Real.dist_eq, hfq] at hh
  refine ⟨r, ⟨hqr,hr1⟩, center_latitude_strong_of_gt μ hQ hq.1.le hqr hr1 hab, ?_⟩
  have ht := (abs_lt.mp hh).1
  change _ < F r
  linarith

/-- The weak strong-field condition a≥b, including its boundary, gives the
same sharp lower height for the literal affine tensor model. -/
theorem latitude_weakStrongField_maximum_lower (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q ≤
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    {ε : ℝ} (hε : 0 < ε) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let a := latitudeDerivativeVariance c q
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)), ‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)), (∀ x, inner ℝ (e x) w=0) →
        disorderLaw (n+3) μ.maxDegree
          {J | ¬ ∃ y, ‖y‖^2=((n+2 : ℕ) : ℝ) ∧
            ((n+3 : ℕ) : ℝ)*(Real.sqrt a-ε)<latitudeField c J w e q y} ≤
          3*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨r,hr,habr,happrox⟩ := exists_strong_latitude_approximation μ hQ hq hab hε
  have hr0 : 0 < r := hq.1.trans hr.1
  have hrabs : |r| < 1 := by rw [abs_of_pos hr0]; exact hr.2
  have hqabs : |q| < 1 := by rw [abs_of_pos hq.1]; exact hq.2
  obtain ⟨η,hη,hmax⟩ := latitude_strongField_maximum_lower μ hQ hr0.ne' hrabs habr (show 0 < ε/2 by positivity)
  refine ⟨min 1 η, lt_min (by norm_num) hη, ?_⟩
  filter_upwards [hmax] with n hn
  intro w hw e he
  let E := {J : Disorder (n+3) μ.maxDegree | ¬ ∃ y, ‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    ((n+3 : ℕ) : ℝ)*(Real.sqrt (latitudeDerivativeVariance c q)-ε)<latitudeField c J w e q y}
  let F := {J : Disorder (n+3) μ.maxDegree | ¬ ∃ y, ‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    ((n+3 : ℕ) : ℝ)*(Real.sqrt (latitudeDerivativeVariance c r)-ε/2)<latitudeField c J w e r y}
  have hN : 0 < ((n+3 : ℕ) : ℝ) := by positivity
  have hsub : E ⊆ (regularDisorder (N := n+3) (P := μ.maxDegree))ᶜ ∪ F := by
    intro J hJ
    by_cases hreg : J ∈ regularDisorder
    · right
      intro hgood
      obtain ⟨y,hy,hyH⟩ := hgood
      have hmod := regularDisorder_latitude_field_modulus c J hreg w hw e he hqabs.le hrabs.le y hy
      have hap := mul_lt_mul_of_pos_left happrox hN
      have hd := (abs_le.mp hmod).1
      apply hJ
      refine ⟨y,hy,?_⟩
      nlinarith
    · exact Or.inl hreg
  have hm : disorderLaw (n+3) μ.maxDegree E ≤
      disorderLaw (n+3) μ.maxDegree (regularDisorder (N := n+3) (P := μ.maxDegree))ᶜ+
        disorderLaw (n+3) μ.maxDegree F :=
    (measure_mono hsub).trans (measure_union_le _ _)
  apply hm.trans
  have hlow := regularDisorder_failure_ennreal (P := μ.maxDegree) (show 2 ≤ n+3 by omega)
  have hhigh := hn w hw e he
  have hg : ENNReal.ofReal (Real.exp (-((n+3 : ℕ) : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-min 1 η*((n+3 : ℕ) : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left 1 η) hN.le]
  have hh : ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-min 1 η*((n+3 : ℕ) : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (min_le_right 1 η) hN.le]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-((n+3 : ℕ) : ℝ)))+
        2*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := add_le_add hlow hhigh
    _ ≤ ENNReal.ofReal (Real.exp (-min 1 η*((n+3 : ℕ) : ℝ)))+
        2*ENNReal.ofReal (Real.exp (-min 1 η*((n+3 : ℕ) : ℝ))) := by gcongr
    _ = _ := by ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
