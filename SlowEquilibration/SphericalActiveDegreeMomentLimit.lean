-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeFiniteResponse
public import SlowEquilibration.CSFiniteMixtureDirectionalDerivative
public import SlowEquilibration.LocalConvexDerivativeLimit

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeMomentLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreePhysicalPressure SphericalActiveDegreeFiniteResponse
open CSFiniteMixtureDirectionalDerivative CSCovarianceDirectionalDerivative
open CSGeneralCovarianceStability SphericalTAPCertificate
open LocalConvexDerivativeLimit
open PureCapturePhysicalFullOverlapArray
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def activeDegreeCSValue (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) (s : ℝ) : ℝ :=
  (locallyPerturbedMinimizer β μ.xi p.val.val
    (perturbationLipschitzConstant μ p.val.val)
    (base_lipschitzOn μ p.val.val)
    (fun t ht => monomial_perturbation_lipschitzOn μ p.val.val
      (abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩))
    ((mixtureCoefficients μ p)*(s^2-1))).value β
    (fun r => μ.xi r+(mixtureCoefficients μ p)*(s^2-1)*r^p.val.val)

theorem certificate_activeDegreeCSValue_hasDerivAt_one
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (p : Degree μ.maxDegree) :
    HasDerivAt (activeDegreeCSValue μ β p)
      (β^2*(mixtureCoefficients μ p)*(1-(1-x)*Q^p.val.val)) 1 := by
  let c := mixtureCoefficients μ p
  let f : ℝ → ℝ := fun t =>
    (locallyPerturbedMinimizer β μ.xi p.val.val
      (perturbationLipschitzConstant μ p.val.val)
      (base_lipschitzOn μ p.val.val)
      (fun s hs => monomial_perturbation_lipschitzOn μ p.val.val
        (abs_le.mpr ⟨by linarith [hs.1],hs.2.le⟩)) t).value β
        (fun r => μ.xi r+t*r^p.val.val)
  have hcs : HasDerivAt f ((β^2/2)*(1-∫ r, r^p.val.val
      ∂(CSParisiMeasure.canonicalMinimizer μ β).law)) 0 :=
    hasDerivAt_finiteMixture_monomial_value μ β p.val.val
  have hcert : deriv f 0 = (β^2/2)*(1-(1-x)*Q^p.val.val) :=
    certificate_monomial_value_derivative h p.val.val (by omega)
  have heq : ((β^2/2)*(1-∫ r, r^p.val.val
      ∂(CSParisiMeasure.canonicalMinimizer μ β).law)) =
      (β^2/2)*(1-(1-x)*Q^p.val.val) := by
    rw [← hcs.deriv, hcert]
  have ht : HasDerivAt (fun s : ℝ => c*(s^2-1)) (2*c) 1 := by
    convert (((hasDerivAt_pow 2 (1:ℝ)).sub_const 1).const_mul c) using 1; ring_nf
  have hczero : c*((1:ℝ)^2-1)=0 := by ring
  have hcs' : HasDerivAt f ((β^2/2)*(1-∫ r, r^p.val.val
      ∂(CSParisiMeasure.canonicalMinimizer μ β).law)) (c*((1:ℝ)^2-1)) := by
    simpa only [hczero] using hcs
  have hc := hcs'.comp 1 ht
  change HasDerivAt (activeDegreeCSValue μ β p)
    (((β^2/2)*(1-∫ r, r^p.val.val
      ∂(CSParisiMeasure.canonicalMinimizer μ β).law))*(2*c)) 1 at hc
  convert hc using 1
  rw [heq]
  dsimp [c]
  ring

/-- For a degree already present with positive variance, ordinary convexity
at physical amplitude one transports the exact finite pair-power response
through a locally perturbed Parisi pressure limit. No zero-probe uniform
quadratic-response assumption is needed. -/
theorem physical_pairPower_tendsto_of_active_degree_parisi
    {μ : FiniteMixture} {β x Q : ℝ} (h : Certificate μ β x Q)
    (hβ : 0 < β) (p : Degree μ.maxDegree)
    (hcp : 0 < mixtureCoefficients μ p)
    (δ : ℝ) (hδ : 0 < δ)
    (hpressure : ∀ s ∈ Ioo (1-δ) (1+δ),
      Tendsto (fun n : ℕ => activeDegreePressure (n+2) μ β p s)
        atTop (𝓝 (activeDegreeCSValue μ β p s))) :
    Tendsto (fun n : ℕ =>
      ∫ c, (c 0 1)^p.val.val ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 ((1-x)*Q^p.val.val)) := by
  have hcs := certificate_activeDegreeCSValue_hasDerivAt_one h p
  have hd := deriv_tendsto_of_convex_local_pointwise
    (fun n s => activeDegreePressure (n+2) μ β p s)
    (activeDegreeCSValue μ β p) 1 δ hδ
    (fun n => activeDegreePressure_convex (by omega) μ β p)
    (fun n => (activeDegreePressure_hasDerivAt_one μ β n p).differentiableAt)
    hpressure hcs.differentiableAt
  rw [hcs.deriv] at hd
  have hA : β^2*(mixtureCoefficients μ p) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 2 hβ.ne') hcp.ne'
  have ht := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from
    tendsto_const_nhds).sub (hd.div_const (β^2*(mixtureCoefficients μ p)))
  convert ht using 1
  · funext n
    rw [(activeDegreePressure_hasDerivAt_one μ β n p).deriv]
    field_simp
    ring
  · field_simp
    ring

end SlowEquilibration.SphericalActiveDegreeMomentLimit
