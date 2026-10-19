-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureKilledProductTest
public import SlowEquilibration.SphericalWeightedProductPairing

/-! The exact actual physical Fh test yields the source weighted energy
inequality before the commutator and averaged-error absorption. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

/-- The literal physical weighted energy inequality follows from the
constructed full-domain Fh test and 0≤h≤1, rather than being assumed. -/
theorem rateLaplace_killing_weighted_energy (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ)
    (F : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (CF : ℝ≥0) (hF : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖F.val.fst x‖ ≤ CF)
    (hF0 : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ F.val.fst x) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F+
        sphericalWeightedGradientCross D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F+
        (∫ x,κ x*F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)+
        (θ : ℝ)*(∫ x,F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian) ≤
        ∫ x,κ x*F.val.fst x ∂gibbsLaw N β D.hamiltonian := by
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  obtain ⟨u,v,hu,hv,hgrad,heq⟩ := rateLaplace_killing_product_test D β κ hκ hκ0 K hK θ hθ F CF hF
  have hu' : u.val.fst=h := hu
  have hunit := rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ
  have hU : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖u.val.fst x‖ ≤ (1 : ℝ≥0) := by
    rw [hu']
    exact hunit.mono (fun _ hx => by rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2)
  have hG : ∀ ij : Fin N × Fin N,v.val.snd ij=ᵐ[gibbsLaw N β D.hamiltonian]
      fun x => u.val.fst x*F.val.snd ij x+F.val.fst x*u.val.snd ij x := by
    simpa only [hu'] using hgrad
  have hpair := sphericalCompletedDirichlet_product_pairing D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous u F v 1 CF hU hF hG
  rw [hpair] at heq
  have hi : Integrable (fun x => κ x*F.val.fst x) (gibbsLaw N β D.hamiltonian) := by
    let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
    apply ((Lp.memLp (killingMultiplication D β κ hκ K hK F.val.fst)).integrable (by norm_num)).congr
    exact multiplication_ae (gibbsLaw N β D.hamiltonian) κ hκ.aestronglyMeasurable K (.of_forall hK) F.val.fst
  have hir : Integrable (fun x => κ x*F.val.fst x*h x) (gibbsLaw N β D.hamiltonian) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (killingVector D β κ hκ) v.val.fst).congr
    filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous κ hκ,hv] with x hx hvx
    change killingVector D β κ hκ x=κ x at hx
    simp only [RCLike.inner_apply,conj_trivial,hx,hvx]
    ring
  have hle : (∫ x,κ x*F.val.fst x*h x ∂gibbsLaw N β D.hamiltonian) ≤
      ∫ x,κ x*F.val.fst x ∂gibbsLaw N β D.hamiltonian := by
    apply integral_mono_ae hir hi
    filter_upwards [hunit,hF0] with x hx hFx
    exact mul_le_of_le_one_right (mul_nonneg (hκ0 x) hFx) hx.2
  exact ⟨u,hu,heq.le.trans hle⟩

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
