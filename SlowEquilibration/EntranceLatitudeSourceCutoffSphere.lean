-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeSourceQuadraticMoments
public import SlowEquilibration.SphericalLatitudeRealDomination

/-! Transport of genuine cutoff source latitude moments to the actual
sphere. The cutoff has its true support and bounded multiplier; the axis
is arbitrary and may depend on the fixed original disorder. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance SphericalTwoPointCovariance
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Continuous cutoff of a genuinely source-dominated correction has its
actual sphere weighted square bounded by the subcritical radial integral. -/
theorem source_cutoff_sphere_square_exp_abs_le {n : ℕ} (hn : 2≤n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0≤Q) {M ζ ρ : ℝ} (hM : 0≤M) (hζ : 0≤ζ)
    (J : Disorder (n+1) μ.maxDegree) (hJ : J∈originalLatitudeMeanGood n μ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (F W : Vector (n+1)→ℝ) (hF : Continuous F) (hW : Continuous W)
    (hFb : ∀ u,‖u‖^2=((n+1 : ℕ) : ℝ) →
      |F u|≤ sourceLatitudeCorrectionConstant μ Q M*
        (((n+1 : ℕ) : ℝ)*|overlap x u|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|overlap x u|^(μ.minDegree-1)*
          |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|))
    (hWb : ∀ u,‖u‖^2=((n+1 : ℕ) : ℝ) → |W u|≤|F u|)
    (hW0 : ∀ u,ρ< |overlap x u| → W u=0)
    (hAbs : ∀ r,|r|≤ρ → sourceLatitudeMomentConstant μ Q M ζ*sourceLatitudeWeightPower n μ r≤
      ((n+1 : ℕ) : ℝ)*r^2/8) :
    Integrable (fun u => (W u)^2*Real.exp (ζ*|W u|)) (sphereLaw (n+1)) ∧
    (∫ u,(W u)^2*Real.exp (ζ*|W u|) ∂sphereLaw (n+1))≤
      sourceLatitudeQuadraticConstant μ Q M ζ*
        (∫ u,sourceLatitudeQuadraticPower n μ (overlap x u)*
          Real.exp (((n+1 : ℕ) : ℝ)*(overlap x u)^2/8) ∂sphereLaw (n+1)) := by
  let G := fun r : ℝ => sourceLatitudeQuadraticConstant μ Q M ζ*sourceLatitudeQuadraticPower n μ r*
    Real.exp (((n+1 : ℕ) : ℝ)*r^2/8)
  have hG : Continuous G := by unfold G sourceLatitudeQuadraticPower;fun_prop
  have hG0 : ∀ r,0≤G r := by
    intro r
    have hc := (sourceLatitudeQuadraticConstant_pos μ Q M ζ).le
    unfold G sourceLatitudeQuadraticPower
    positivity
  have hT : Continuous (fun u => (W u)^2*Real.exp (ζ*|W u|)) :=
    (hW.pow 2).mul ((hW.abs.const_mul ζ).rexp)
  have h := latitude_integral_domination hn x hx _ hT (fun u => by positivity) G hG hG0 ?_
  · refine ⟨h.1,?_⟩
    apply h.2.trans_eq
    have heqG : (fun u : Vector (n+1) => G (overlap x u))=
        (fun u => sourceLatitudeQuadraticConstant μ Q M ζ*(sourceLatitudeQuadraticPower n μ (overlap x u)*
          Real.exp (((n+1 : ℕ) : ℝ)*(overlap x u)^2/8))) := by
      funext u
      unfold G
      ring
    rw [heqG]
    exact integral_const_mul _ _
  · intro r hr
    let ν := latitudeLaw x (latitudeFrameAt x) r
    have hsup := latitudeLaw_support (by omega : 1≤n) x hx (latitudeFrameAt x)
      (latitudeFrameAt_orthogonal x hx) (abs_lt.mpr hr).le
    have hiW : Integrable (fun u => (W u)^2*Real.exp (ζ*|W u|)) ν :=
      integrable_sphereSupported_continuous ν (hsup.mono (fun u hu => hu.1)) hT
    refine ⟨hiW,?_⟩
    by_cases hcap : |r|≤ρ
    · have hd : ∀ᵐ u ∂ν,|F u|≤ sourceLatitudeCorrectionConstant μ Q M*
          (((n+1 : ℕ) : ℝ)*|r|^μ.minDegree+Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)*
            |observable (centerCoefficients (mixtureCoefficients μ) Q) J x u|) := by
        filter_upwards [hsup] with u hu
        have hf := hFb u hu.1
        rw [overlap_comm u x,hu.2] at hf
        exact hf
      have hq := latitude_source_dominated_square_exp_abs_le (by omega) μ hQ hM hζ J hJ x hx hr F hF hd
      have hdom : ∀ᵐ u ∂ν,(W u)^2*Real.exp (ζ*|W u|)≤(F u)^2*Real.exp (ζ*|F u|) := by
        filter_upwards [hsup] with u hu
        have hb := hWb u hu.1
        have hs := (sq_le_sq₀ (abs_nonneg (W u)) (abs_nonneg (F u))).mpr hb
        rw [sq_abs,sq_abs] at hs
        exact mul_le_mul hs (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb hζ))
          (Real.exp_pos _).le (sq_nonneg _)
      apply ((integral_mono_ae hiW hq.1 hdom).trans hq.2).trans
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hAbs r hcap))
        (by have hc := (sourceLatitudeQuadraticConstant_pos μ Q M ζ).le;unfold sourceLatitudeQuadraticPower;positivity)
    · have hz : (fun u => (W u)^2*Real.exp (ζ*|W u|))=ᵐ[ν] fun _ => (0 : ℝ) := by
        filter_upwards [hsup] with u hu
        have ho : overlap x u=r := by rw [overlap_comm u x,hu.2]
        rw [hW0 u (by rw [ho];exact lt_of_not_ge hcap)]
        simp
      rw [integral_congr_ae hz,integral_zero]
      exact hG0 r

end
end SlowEquilibration.EntranceLatitudeTangentObservable
