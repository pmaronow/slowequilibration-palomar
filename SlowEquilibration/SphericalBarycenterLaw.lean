module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenter

@[expose] public section

/-! # The actual overlap-reweighted Gibbs probability law -/

namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators ENNReal
variable {N : ℕ}

/-- The literal normalized overlap-reweighted Gibbs density. -/
def weightedDensity (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ) (x u : Vector N) : ℝ :=
  (psi h x u)^2 / denominator β H h x

/-- The literal source law w_x with density ψ²/d against actual Gibbs. -/
def weightedLaw (β : ℝ) (H : Vector N → ℝ) (h : ℝ → ℝ) (x : Vector N) : Measure (Vector N) :=
  (gibbsLaw N β H).withDensity (fun u => ENNReal.ofReal (weightedDensity β H h x u))

lemma weightedDensity_pos (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x u : Vector N) :
    0 < weightedDensity β H h x u :=
  div_pos (sq_pos_of_pos (psi_pos h x u)) (denominator_pos hN β hH hh x)

lemma weightedDensity_continuous (β : ℝ) (H : Vector N → ℝ)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    Continuous (weightedDensity β H h x) :=
  (((psi_joint_contDiff hh).continuous.comp (continuous_id.prodMk continuous_const)).pow 2).div_const _

/-- Probability normalization is computed from the actual denominator
integral, rather than required of a supplied reweighted law. -/
theorem weightedLaw_probability (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    IsProbabilityMeasure (weightedLaw β H h x) := by
  let := gibbsLaw_probability hN β hH
  have hi : Integrable (weightedDensity β H h x) (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH (weightedDensity_continuous β H hh x)
  constructor
  rw [weightedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ (fun u => (weightedDensity_pos hN β hH hh x u).le))]
  unfold weightedDensity
  rw [integral_div]
  change ENNReal.ofReal (denominator β H h x / denominator β H h x) = 1
  rw [div_self (denominator_pos hN β hH hh x).ne', ENNReal.ofReal_one]

lemma weightedLaw_support (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (h : ℝ → ℝ) (x : Vector N) :
    ∀ᵐ u ∂weightedLaw β H h x, ‖u‖^2 = (N:ℝ) :=
  (gibbsLaw_support hN β H).filter_mono
    (withDensity_absolutelyContinuous (μ := gibbsLaw N β H)
      (f := fun u => ENNReal.ofReal (weightedDensity β H h x u))).ae_le

/-- Exact ordinary integral formula for the true reweighted law, also
for genuine vector-valued observables. -/
theorem integral_weightedLaw {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N)
    (f : Vector N → G) :
    (∫ u, f u ∂weightedLaw β H h x) =
      (denominator β H h x)⁻¹ • (∫ u, (psi h x u)^2 • f u ∂gibbsLaw N β H) := by
  rw [weightedLaw, integral_withDensity_eq_integral_toReal_smul
    (weightedDensity_continuous β H hh x).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (weightedDensity_pos hN β hH hh x _).le]
  have he : (fun u => weightedDensity β H h x u • f u) =
      (fun u => (denominator β H h x)⁻¹ • ((psi h x u)^2 • f u)) := by
    funext u
    rw [weightedDensity, div_eq_inv_mul, mul_smul]
  rw [he, integral_smul]

/-- The actual barycenter is literally the mean of the normalized spin
under the constructed actual probability law w_x. -/
theorem barycenter_eq_integral (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    barycenter β H h x = ∫ u, spin u ∂weightedLaw β H h x := by
  rw [integral_weightedLaw hN β hH hh x]
  rfl

end
end SlowEquilibration.SphericalBarycenter
