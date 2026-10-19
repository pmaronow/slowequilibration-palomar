-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeWeakStrongField
public import SlowEquilibration.CSAuxiliaryDiracCertificate
public import SlowEquilibration.SphericalLatitudeTransport

@[expose] public section

/-! The actual Huang--Sellke bottom point at the source reference overlap.
It is a point of the original tensor field, with the exact norm and overlap;
its sharp energy lower bound follows from the proved weak strong-field
maximum theorem and the genuine qStar plateau/stability certificate. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression
open scoped ENNReal Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem auxiliary_bottom_variances (μ : FiniteMixture) {q : ℝ} (hq : 0 ≤ q) :
    latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) q) (Real.sqrt q)=
      q*(1-q)*μ.xi1 q ∧
    latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) q) (Real.sqrt q)=
      q^2*(1-q)^2*μ.xi2 q := by
  constructor
  · rw [latitudeDerivativeVariance, Real.sq_sqrt hq, firstCovariance_center, firstCovariance_mixture]
    ring
  · rw [latitudeCurvatureVariance, Real.sq_sqrt hq, secondCovariance_center, secondCovariance_mixture]
    ring

theorem auxiliary_bottom_weakStrongField (μ : FiniteMixture) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (he : μ.elasticity q ≤ 1/(1-q)) :
    latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) q) (Real.sqrt q) ≤
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) q) (Real.sqrt q) := by
  rw [(auxiliary_bottom_variances μ hq.1.le).1, (auxiliary_bottom_variances μ hq.1.le).2]
  change q*μ.xi2 q/μ.xi1 q ≤ 1/(1-q) at he
  have hh := (div_le_div_iff₀ (μ.xi1_pos hq.1) (sub_pos.mpr hq.2)).mp he
  have ht := mul_le_mul_of_nonneg_left hh (mul_nonneg hq.1.le (sub_nonneg.mpr hq.2.le))
  convert ht using 1 <;> ring

theorem auxiliary_bottom_energy (μ : FiniteMixture) {q β : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hβ : 0 < β) (hp : β^2*μ.xi1 q=q/(1-q)) :
    β*Real.sqrt (latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) q) (Real.sqrt q))=q := by
  rw [(auxiliary_bottom_variances μ hq.1.le).1]
  have ha : 0 < q*(1-q)*μ.xi1 q := mul_pos (mul_pos hq.1 (sub_pos.mpr hq.2)) (μ.xi1_pos hq.1)
  apply (sq_eq_sq₀ (mul_nonneg hβ.le (Real.sqrt_nonneg _)) hq.1.le).mp
  rw [mul_pow, Real.sq_sqrt ha.le]
  calc
    _ = q*(1-q)*(β^2*μ.xi1 q) := by ring
    _ = q^2 := by rw [hp]; field_simp [(sub_pos.mpr hq.2).ne']

/-- A genuine point of the original Hamiltonian with squared norm NqStar,
overlap qStar with the reference, and βH/N arbitrarily close to qStar. -/
theorem actual_auxiliary_bottom_maximum_lower (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) {ε : ℝ} (hε : 0 < ε) :
    let q := Thresholds.qStar μ.xi β
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (w : Vector (n+3)), ‖w‖^2=((n+3 : ℕ) : ℝ) →
        disorderLaw (n+3) μ.maxDegree
          {J | ¬ ∃ x : Vector (n+3), ‖x‖^2=((n+3 : ℕ) : ℝ)*q ∧ overlap x w=q ∧
            ((n+3 : ℕ) : ℝ)*(q-ε)<β*fieldOfMixture μ J x} ≤
          3*ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) q
  have hq : q ∈ Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have hβ0 : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hp : β^2*μ.xi1 q=q/(1-q) := by
    have hh := (μ.qStar_solves_plateau hβ).2
    change β^2*deriv μ.xi q=q/(1-q) at hh
    rw [(μ.hasDerivAt_xi q).deriv] at hh
    exact hh
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq.1
  have hs1 : Real.sqrt q < 1 := by
    have hs := Real.sq_sqrt hq.1.le
    nlinarith [Real.sqrt_nonneg q, hq.2]
  have hab := auxiliary_bottom_weakStrongField μ hq (μ.elasticity_qStar_le hβ)
  have henergy := auxiliary_bottom_energy μ hq hβ0 hp
  obtain ⟨η,hη,hmax⟩ := latitude_weakStrongField_maximum_lower μ hq.1 ⟨hs0,hs1⟩ hab
    (show 0 < ε/β by positivity)
  refine ⟨η,hη,?_⟩
  filter_upwards [hmax] with n hn
  intro w hw
  let e := latitudeFrameAt w
  have he : ∀ y, inner ℝ (e y) w=0 := latitudeFrameAt_orthogonal w hw
  apply le_trans (measure_mono ?_) (hn w hw e he)
  intro J hJ
  change ¬ ∃ y, ‖y‖^2=((n+2 : ℕ) : ℝ) ∧
    ((n+3 : ℕ) : ℝ)*(Real.sqrt (latitudeDerivativeVariance c (Real.sqrt q))-ε/β)<
      latitudeField c J w e (Real.sqrt q) y
  intro hgood
  obtain ⟨y,hy,hyH⟩ := hgood
  let z := latitudeMap w e (Real.sqrt q) y
  let x := Real.sqrt q • z
  have hsabs : |Real.sqrt q| ≤ 1 := by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hs1.le
  have hz : ‖z‖^2=((n+3 : ℕ) : ℝ) := latitudeMap_norm_sq (by omega) w hw e he hsabs y hy
  have hx : ‖x‖^2=((n+3 : ℕ) : ℝ)*q := by
    dsimp only [x]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt hq.1.le, hz]
    ring
  have hR : overlap x w=q := by
    dsimp only [x,overlap]
    rw [inner_smul_left, mul_div_assoc]
    change Real.sqrt q*overlap z w=q
    rw [overlap_latitude_center w hw e he, ← pow_two, Real.sq_sqrt hq.1.le]
  have hfield : latitudeField c J w e (Real.sqrt q) y=fieldOfMixture μ J x := by
    exact field_center_scale (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) hq.1.le J z
  apply hJ
  refine ⟨x,hx,hR,?_⟩
  rw [← hfield]
  have ht := mul_lt_mul_of_pos_left hyH hβ0
  have herr : β*(ε/β)=ε := by field_simp
  calc
    _ = β*(((n+3 : ℕ) : ℝ)*(Real.sqrt (latitudeDerivativeVariance c (Real.sqrt q))-ε/β)) := by
      change _=β*(((n+3 : ℕ) : ℝ)*(Real.sqrt (latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) q) (Real.sqrt q))-ε/β))
      nlinarith [henergy]
    _ < _ := ht

end
end SlowEquilibration.SphericalLatitudeChartKacRice
