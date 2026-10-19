-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSobolevScalarChain
public import SlowEquilibration.SphericalSmoothScalarLocalizations

/-! The literal logarithm chain rule for bounded completed spherical
Sobolev functions bounded below by one. Scalar smooth localization is
constructed, rather than a log chain interface being assumed. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance.KilledOperator SphericalSmoothScalarLocalizations
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {β : ℝ} {H : Vector N → ℝ}

theorem lp_inv_norm_le_one {μ : Measure (Vector N)} (U : Lp ℝ 2 μ)
    (hU : ∀ᵐ x ∂μ,1 ≤ U x) : ∀ᵐ x ∂μ,‖(U x)⁻¹‖ ≤ 1 := by
  filter_upwards [hU] with x hx
  rw [Real.norm_eq_abs,abs_inv,abs_of_pos (by linarith : 0 < U x)]
  exact inv_le_one_of_one_le₀ hx

def logGradientMultiplier (U : Lp ℝ 2 (gibbsLaw N β H))
    (hU : ∀ᵐ x ∂gibbsLaw N β H,1 ≤ U x)
    (G : PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H))) :
    PiLp 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H)) :=
  WithLp.toLp 2 (fun ij => multiplication (gibbsLaw N β H) (fun x => (U x)⁻¹)
    ((measurable_inv.comp_aemeasurable (Lp.aestronglyMeasurable U).aemeasurable).aestronglyMeasurable) 1 (lp_inv_norm_le_one U hU) (G ij))

/-- The completed graph contains log F with its actual inverse-F gradient,
proved for every bounded F≥1 in the real spherical Sobolev domain. -/
theorem sphericalSobolevGraph_log_chain (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H)
    (u : sphericalSobolevGraph hN β H hH) (C : ℝ) (hC : 1 ≤ C)
    (hu : ∀ᵐ x ∂gibbsLaw N β H,1 ≤ u.val.fst x ∧ u.val.fst x ≤ C) :
    ∃ v : sphericalSobolevGraph hN β H hH,
      (v.val.fst =ᵐ[gibbsLaw N β H] fun x => Real.log (u.val.fst x)) ∧
      v.val.snd=logGradientMultiplier u.val.fst (hu.mono (fun _ hx => hx.1)) u.val.snd := by
  obtain ⟨Φ,hΦ,hΦ0,⟨K,hK⟩,hΦeq⟩ := exists_log_localization C hC
  obtain ⟨v,hvValue,hvGradient⟩ := sphericalSobolevGraph_scalar_chain hN β H hH Φ hΦ hΦ0 K hK u
  let hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by simp)
  let hL := lipschitzWith_of_nnnorm_deriv_le (hΦ1.differentiable (by norm_num))
    (fun r => show ‖deriv Φ r‖₊ ≤ K from hK r)
  refine ⟨v,?_ ,?_⟩
  · rw [hvValue]
    filter_upwards [hL.coeFn_compLp hΦ0 u.val.fst,hu] with x hx hux
    exact hx.trans (hΦeq _ hux).1
  · rw [hvGradient]
    apply PiLp.ext
    intro ij
    apply Lp.ext
    filter_upwards [hu,
      multiplication_ae (gibbsLaw N β H) (fun x => deriv Φ (u.val.fst x))
        ((hΦ1.continuous_deriv_one).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u.val.fst))
        K (.of_forall (fun x => hK _)) (u.val.snd ij),
      multiplication_ae (gibbsLaw N β H) (fun x => (u.val.fst x)⁻¹)
        ((measurable_inv.comp_aemeasurable (Lp.aestronglyMeasurable u.val.fst).aemeasurable).aestronglyMeasurable) 1
        (lp_inv_norm_le_one u.val.fst (hu.mono (fun _ hx => hx.1))) (u.val.snd ij)]
        with x hux hleft hright
    change multiplication (gibbsLaw N β H) (fun x => deriv Φ (u.val.fst x))
      ((hΦ1.continuous_deriv_one).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u.val.fst))
      K (.of_forall (fun x => hK _)) (u.val.snd ij) x=
      multiplication (gibbsLaw N β H) (fun x => (u.val.fst x)⁻¹)
        ((measurable_inv.comp_aemeasurable (Lp.aestronglyMeasurable u.val.fst).aemeasurable).aestronglyMeasurable) 1
        (lp_inv_norm_le_one u.val.fst (hu.mono (fun _ hx => hx.1))) (u.val.snd ij) x
    rw [hleft,hright,(hΦeq _ hux).2]

end SlowEquilibration.SphericalForm
