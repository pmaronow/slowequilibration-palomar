-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
public import SlowEquilibration.SphericalLatitudeCoarea

@[expose] public section

/-! Integrating the physical pointwise symmetric-latitude estimate over an
actual transverse angular law. The source regularity event and the final
coarea identification are separate from this deterministic step. -/

namespace SlowEquilibration.SphericalTAPPhysicalShellLower
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalTAPPhysicalLatitudeSlice
set_option autoImplicit false

/-- The transverse vector of the round latitude law, at the physical
spherical radius, expressed in the chart's isometric tangent frame. -/
def physicalTransverse (n : ℕ) (x : Vector n) : Vector (n+1) :=
  Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)) • latitudeChartFrame n x

/-- The physical latitude slice really evaluates the original Hamiltonian
at the same point as the normalized round latitude law. -/
theorem latitudeMap_eq_physicalSlicePoint
    (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : |a| ≤ 1) (x : Vector n) :
    latitudeMap (latitudeChartPole n) (latitudeChartFrame n) a x =
      a • latitudeChartPole n + Real.sqrt (1-a^2) • physicalTransverse n x := by
  have hnonneg : 0 ≤ 1-a^2 := by
    rw [abs_le] at ha
    nlinarith [ha.1, ha.2]
  have hratio : 0 ≤ (((n+1:ℕ):ℝ)/(n:ℝ)) := by positivity
  simp only [latitudeMap, physicalTransverse, smul_smul]
  rw [Real.sqrt_mul hratio]
  ring

theorem physicalLatitudeSlice_eq_originalLatitudeField
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    (J : Disorder (n+1) μ.maxDegree) (a : ℝ) (ha : |a| ≤ 1)
    (x : Vector n) :
    physicalLatitudeSlice n μ (latitudeChartPole n)
      (physicalTransverse n x) J a =
      field (mixtureCoefficients μ) J
        (latitudeMap (latitudeChartPole n) (latitudeChartFrame n) a x) := by
  unfold physicalLatitudeSlice
  rw [latitudeMap_eq_physicalSlicePoint n hn a ha x]

/-- The original polynomial Hamiltonian and exact spherical entropy give a
lower bound after averaging over any finite transverse law. In particular,
this applies to the normalized round angular law once its regularity event
and integrability are established. -/
theorem physicalLatitudeExponent_shell_lower
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (n : ℕ) (hn : 2 ≤ n) (μ : FiniteMixture)
    (u : Vector (n+1)) (ω : Ω → Vector (n+1))
    (J : Disorder (n+1) μ.maxDegree)
    {r center width β C₀ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hwidth : 0 < width)
    (hβ : 0 ≤ β) (hC₀ : 0 ≤ C₀)
    (hinside : ∀ a ∈ Icc (center-width) (center+width), |a| ≤ r)
    (hfield : ∀ v a, a ∈ Icc (center-width) (center+width) →
      |iteratedDeriv 2 (physicalLatitudeSlice n μ u (ω v) J) a| ≤
        C₀*((n+1:ℕ):ℝ))
    (hcentral : Integrable (fun v =>
      Real.exp (physicalLatitudeExponent n μ u (ω v) J β center)) ν)
    (hshell : Integrable (fun v =>
      ∫ a in (center-width)..(center+width),
        Real.exp (physicalLatitudeExponent n μ u (ω v) J β a)) ν) :
    (2*width*Real.exp (-(((n+1:ℕ):ℝ)*
      (β*C₀+2/(1-r^2)^2))*width^2/2))*
      (∫ v, Real.exp (physicalLatitudeExponent n μ u (ω v) J β center) ∂ν) ≤
        ∫ v, (∫ a in (center-width)..(center+width),
          Real.exp (physicalLatitudeExponent n μ u (ω v) J β a)) ∂ν := by
  let curvature : ℝ := ((n+1:ℕ):ℝ)*(β*C₀+2/(1-r^2)^2)
  have hden : 0 < (1-r^2)^2 := by
    apply sq_pos_of_pos
    nlinarith [hr0, hr1]
  have hcurvature : 0 ≤ curvature := by
    dsimp [curvature]
    positivity
  let c : ℝ := 2*width*Real.exp (-curvature*width^2/2)
  have hpoint (v : Ω) :
      c*Real.exp (physicalLatitudeExponent n μ u (ω v) J β center) ≤
        ∫ a in (center-width)..(center+width),
          Real.exp (physicalLatitudeExponent n μ u (ω v) J β a) := by
    have h := physicalLatitudeExponent_symmetric_integral_lower
      n hn μ u (ω v) J hr0 hr1 hwidth hβ hinside (hfield v)
    have hf : 2*width*Real.exp
        (physicalLatitudeExponent n μ u (ω v) J β center-
          curvature*width^2/2) =
        c*Real.exp (physicalLatitudeExponent n μ u (ω v) J β center) := by
      dsimp [c]
      rw [show physicalLatitudeExponent n μ u (ω v) J β center-
        curvature*width^2/2 = -curvature*width^2/2 +
          physicalLatitudeExponent n μ u (ω v) J β center by ring,
        Real.exp_add]
      ring
    rw [hf] at h
    exact h
  have hbound := integral_mono_ae (hcentral.const_mul c) hshell
    (Filter.Eventually.of_forall hpoint)
  simpa only [integral_const_mul, c, curvature] using hbound

end
end SlowEquilibration.SphericalTAPPhysicalShellLower
