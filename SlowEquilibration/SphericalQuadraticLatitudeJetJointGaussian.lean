-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetCenterOrthogonality

@[expose] public section

/-! Finite-dimensional joint Gaussian independence for the actual second
Taylor latitude bank and the complete finite center observation. This is an
unconditional identity for the original tensor disorder. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open scoped RealInnerProductSpace
set_option autoImplicit false

def quadraticLatitudeJetFamily {N k : ℕ} (μ : FiniteMixture) (a : ℝ)
    (u : Vector N) (ω : Fin k → Vector N) (J : Disorder N μ.maxDegree) :
    Fin k → ℝ := fun i => quadraticLatitudeJet μ a u (ω i) J

def quadraticLatitudeJetFamilyCLM {N k : ℕ} (μ : FiniteMixture) (a : ℝ)
    (u : Vector N) (ω : Fin k → Vector N) :
    Disorder N μ.maxDegree →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    ((1-a^2)/2) • jetCLM (mixtureCoefficients μ) 2 (a • u) ![ω i,ω i])

@[simp] theorem quadraticLatitudeJetFamilyCLM_apply {N k : ℕ}
    (μ : FiniteMixture) (a : ℝ) (u : Vector N) (ω : Fin k → Vector N)
    (J : Disorder N μ.maxDegree) :
    quadraticLatitudeJetFamilyCLM μ a u ω J =
      quadraticLatitudeJetFamily μ a u ω J := by
  funext i
  simp [quadraticLatitudeJetFamilyCLM, quadraticLatitudeJetFamily,
    quadraticLatitudeJet]

/-- Every finite family of the genuine quadratic-bank probes is jointly
independent of the center value and any finite collection of its directional
gradients, including the extensive radial mark and all tangent coordinates. -/
theorem quadraticLatitudeJetFamily_independent_center_valueGradient
    {N k d : ℕ} (hN : 0 < N) (μ : FiniteMixture)
    (hμ : 3 ≤ μ.minDegree) (a : ℝ) (u : Vector N)
    (ω : Fin k → Vector N) (hω : ∀ i, inner ℝ (ω i) u=0)
    (w : Fin d → Vector N) :
    IndepFun (quadraticLatitudeJetFamily μ a u ω)
      (valueGradient (mixtureCoefficients μ) u w)
      (disorderLaw N μ.maxDegree) := by
  have hraw := (disorder_hasGaussianLaw N μ.maxDegree).map_fun
    ((quadraticLatitudeJetFamilyCLM μ a u ω).prod
      (valueGradientCLM (mixtureCoefficients μ) u w))
  have hjoint := hraw.congr
    (Y := fun J : Disorder N μ.maxDegree =>
      (quadraticLatitudeJetFamily μ a u ω J,
        valueGradient (mixtureCoefficients μ) u w J))
    (Filter.Eventually.of_forall (fun J => by simp))
  apply hjoint.indepFun_of_covariance_eval
  intro i j
  cases j with
  | none =>
    exact quadraticLatitudeJet_center_value_covariance_zero hN μ a u (ω i) (hω i)
  | some j =>
    exact quadraticLatitudeJet_center_tangent_covariance_zero hN μ hμ a u
      (ω i) (w j) (hω i)

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
