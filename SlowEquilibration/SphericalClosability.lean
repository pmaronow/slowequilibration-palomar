module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalRotationGenerator

@[expose] public section

/-!
# Genuine L² closability of spherical rotation derivatives

The Gibbs law and derivatives are the actual constructed objects. Smooth
ambient tests are dense for this finite Borel measure, and weighted spherical
integration by parts proves that every rotation derivative is closable.
-/

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology ContDiff

/-- Continuous spherical observables belong to the actual Gibbs L² space. -/
theorem memLp_gibbs_of_continuous {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f : Vector N → ℝ} (hH : Continuous H) (hf : Continuous f) :
    MemLp f 2 (gibbsLaw N β H) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (integrable_gibbs_of_continuous hN β hH (hf.pow 2))

/-- A continuous ambient representative in the actual spherical Gibbs L². -/
def gibbsToL2 {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f : Vector N → ℝ) (hf : Continuous f) :
    Lp ℝ 2 (gibbsLaw N β H) := (memLp_gibbs_of_continuous hN β hH hf).toLp f

theorem gibbsToL2_coe {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f : Vector N → ℝ) (hf : Continuous f) :
    gibbsToL2 hN β H hH f hf =ᵐ[gibbsLaw N β H] f :=
  (memLp_gibbs_of_continuous hN β hH hf).coeFn_toLp

theorem gibbsToL2_inner {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f g : Vector N → ℝ) (hf : Continuous f) (hg : Continuous g) :
    inner ℝ (gibbsToL2 hN β H hH f hf) (gibbsToL2 hN β H hH g hg) =
      ∫ x, f x * g x ∂gibbsLaw N β H := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gibbsToL2_coe hN β H hH f hf, gibbsToL2_coe hN β H hH g hg] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

/-- Smooth ambient functions are dense in the actual singular spherical
Gibbs L² law, without a chart-volume identification assumption. -/
theorem gibbsToL2_smooth_dense {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    DenseRange (fun g : {f : Vector N → ℝ // ContDiff ℝ ∞ f} =>
      gibbsToL2 hN β H hH g.val g.property.continuous) := by
  let := gibbsLaw_probability hN β hH
  have hd := Lp.dense_hasCompactSupport_contDiff (F := ℝ) (E := Vector N)
    (μ := gibbsLaw N β H) (p := 2) (by norm_num)
  apply hd.mono
  intro u hu
  obtain ⟨g, hug, _, hg⟩ := hu
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Lp.ext
  exact (gibbsToL2_coe hN β H hH g hg.continuous).trans hug.symm

/-- If smooth observables tend to zero in the actual Gibbs L² space and
one genuine skew rotation derivative tends in L² to `v`, then `v=0`.
This is the exact sequential closability criterion for that derivative. -/
theorem lieDerivative_closable {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (A : Operator N) (hA : star A = -A)
    (f : ℕ → Vector N → ℝ) (hf : ∀ n, ContDiff ℝ 1 (f n))
    (v : Lp ℝ 2 (gibbsLaw N β H))
    (hu : Tendsto (fun n => gibbsToL2 hN β H hH.continuous (f n) (hf n).continuous)
      atTop (𝓝 0))
    (hdu : Tendsto (fun n => gibbsToL2 hN β H hH.continuous (lieDerivative A (f n))
        (lieDerivative_continuous A (hf n))) atTop (𝓝 v)) : v = 0 := by
  have htest (g : Vector N → ℝ) (hg : ContDiff ℝ ∞ g) :
      inner ℝ v (gibbsToL2 hN β H hH.continuous g hg.continuous) = 0 := by
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
    let q := fun x => lieDerivative A g x + β * g x * lieDerivative A H x
    have hq : Continuous q :=
      (lieDerivative_continuous A hg1).add
        ((continuous_const.mul hg.continuous).mul (lieDerivative_continuous A hH))
    have he (n : ℕ) :
        inner ℝ (gibbsToL2 hN β H hH.continuous (lieDerivative A (f n))
          (lieDerivative_continuous A (hf n)))
          (gibbsToL2 hN β H hH.continuous g hg.continuous) =
        -inner ℝ (gibbsToL2 hN β H hH.continuous (f n) (hf n).continuous)
          (gibbsToL2 hN β H hH.continuous q hq) := by
      rw [gibbsToL2_inner, gibbsToL2_inner]
      have hi := gibbs_lie_integration_by_parts hN β hH hg1 (hf n) A hA
      convert hi using 1
      congr 1
      funext x
      exact mul_comm _ _
    have hleft := hdu.inner (𝕜 := ℝ) (tendsto_const_nhds (x :=
      gibbsToL2 hN β H hH.continuous g hg.continuous))
    have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x :=
      gibbsToL2 hN β H hH.continuous q hq))).neg
    simp only [inner_zero_left, neg_zero] at hright
    have heq : (fun n => inner ℝ (gibbsToL2 hN β H hH.continuous (lieDerivative A (f n))
          (lieDerivative_continuous A (hf n)))
          (gibbsToL2 hN β H hH.continuous g hg.continuous)) =
        (fun n => -inner ℝ (gibbsToL2 hN β H hH.continuous (f n) (hf n).continuous)
          (gibbsToL2 hN β H hH.continuous q hq)) := funext he
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  exact (gibbsToL2_smooth_dense hN β H hH.continuous).induction_on
    (p := fun w => inner ℝ v w = 0) v
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    (fun g => htest g.val g.property)

end
end SlowEquilibration.SphericalForm
