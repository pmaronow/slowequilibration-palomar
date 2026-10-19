-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPressureConvex

/-! At a differentiability point of a pointwise convex thermodynamic
limit, the finite-volume derivatives converge. The result is stated for
general convex functions so it also applies to other pressure families. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalConvexDerivativeLimit

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open PureCapturePhysicalPairPressureDerivative
open PureCapturePhysicalPressureConvex
open PureCapturePhysicalFullOverlapArray
open PureCapturePhysicalPairMeanWeakLimit
open PureCapturePhysicalAsymptoticFullLift
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem deriv_tendsto_of_convex_pointwise
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (β : ℝ)
    (hconv : ∀ n, ConvexOn ℝ univ (f n))
    (hdiff : ∀ n, DifferentiableAt ℝ (f n) β)
    (hpoint : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
    (hg : DifferentiableAt ℝ g β) :
    Tendsto (fun n => deriv (f n) β) atTop (𝓝 (deriv g β)) := by
  have hslope (a b : ℝ) :
      Tendsto (fun n => slope (f n) a b) atTop (𝓝 (slope g a b)) := by
    simpa only [slope_def_field] using
      ((hpoint b).sub (hpoint a)).div_const (b - a)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    have hs : Tendsto (slope g β) (𝓝[<] β) (𝓝 (deriv g β)) :=
      (hg.hasDerivAt.tendsto_slope).mono_left (nhdsLT_le_nhdsNE β)
    obtain ⟨a, hca, ha⟩ :=
      ((tendsto_order.1 hs).1 c hc).and self_mem_nhdsWithin |>.exists
    have hsl : ∀ᶠ n in atTop, c < slope (f n) a β := by
      have hca' : c < slope g a β := by rwa [slope_comm] at hca
      exact (tendsto_order.1 (hslope a β)).1 c hca'
    filter_upwards [hsl] with n hn
    exact hn.trans_le ((hconv n).slope_le_deriv (mem_univ a)
      (mem_univ β) ha (hdiff n))
  · intro c hc
    have hs : Tendsto (slope g β) (𝓝[>] β) (𝓝 (deriv g β)) :=
      (hg.hasDerivAt.tendsto_slope).mono_left (nhdsGT_le_nhdsNE β)
    obtain ⟨b, hbc, hb⟩ :=
      ((tendsto_order.1 hs).2 c hc).and self_mem_nhdsWithin |>.exists
    have hsr : ∀ᶠ n in atTop, slope (f n) β b < c :=
      (tendsto_order.1 (hslope β b)).2 c hbc
    filter_upwards [hsr] with n hn
    exact ((hconv n).deriv_le_slope (mem_univ β)
      (mem_univ b) hb (hdiff n)).trans_lt hn

/-- Pointwise convergence of the physical pressure near a differentiability
point determines the actual two-replica covariance mean. -/
theorem physicalPairCovarianceMean_tendsto_of_pressure_limit
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β) :
    Tendsto (fun n : ℕ =>
      ∫ c, μ.xi (c 0 1) ∂(physicalFullOverlapLaw
        (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))
      atTop (𝓝 (μ.xi 1 - deriv p β / β)) := by
  have hd : Tendsto (fun n : ℕ => deriv (quenchedPressure (n+2) μ) β)
      atTop (𝓝 (deriv p β)) :=
    deriv_tendsto_of_convex_pointwise
      (fun n => quenchedPressure (n+2) μ) p β
      (fun n => quenchedPressure_convexOn μ (by omega))
      (fun n => (quenchedPressure_differentiable (by omega) μ) β)
      hp hpdiff
  have hm := (show Tendsto (fun _ : ℕ => μ.xi 1) atTop
      (𝓝 (μ.xi 1)) from tendsto_const_nhds).sub (hd.div_const β)
  convert hm using 1
  ext n
  rw [quenchedPressure_deriv_eq_physicalPairCovarianceMean]
  field_simp
  ring

/-- Consequently every asymptotic full-array limit has the pressure's
derivative-determined covariance mean. -/
theorem asymptoticPairCovarianceMean_eq_of_pressure_limit
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    {x : FullOverlapLawArray}
    (hx : x ∈ physicalFullAsymptoticLimitSet μ β) :
    (∫ c, μ.xi (c 0 1) ∂(x 2 : Measure (FullOverlapCoordinates 2))) =
      μ.xi 1 - deriv p β / β :=
  asymptoticPairCovarianceMean_eq_of_physical_tendsto μ β _
    (physicalPairCovarianceMean_tendsto_of_pressure_limit μ hβ p hp hpdiff) hx

end SlowEquilibration.PureCapturePhysicalConvexDerivativeLimit
