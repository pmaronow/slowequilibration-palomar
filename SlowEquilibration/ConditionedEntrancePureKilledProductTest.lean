-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralKillingFormEquation
public import SlowEquilibration.SphericalSobolevBoundedProductPointwise

/-! The literal Fh test of the actual C² field physical killed
resolvent, constructed in the actual completed spherical form domain. -/
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

/-- The full physical equation can be tested by the actual bounded
completed product Fh, with its literal Leibniz gradient and killing terms.
No product-domain/test identity is supplied. -/
theorem rateLaplace_killing_product_test (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ)
    (F : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (CF : ℝ≥0) (hF : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖F.val.fst x‖ ≤ CF) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u v : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      (v.val.fst=ᵐ[gibbsLaw N β D.hamiltonian] fun x => F.val.fst x*h x) ∧
      (∀ ij : Fin N × Fin N,v.val.snd ij=ᵐ[gibbsLaw N β D.hamiltonian]
        fun x => h x*F.val.snd ij x+F.val.fst x*u.val.snd ij x) ∧
      sphericalCompletedDirichlet D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u v+
        (∫ x,κ x*F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)+
        (θ : ℝ)*(∫ x,F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)=
        ∫ x,κ x*F.val.fst x*h x ∂gibbsLaw N β D.hamiltonian := by
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  obtain ⟨u,hu,hweak⟩ := rateLaplace_killing_formEquation D β κ hκ hκ0 K hK θ hθ
  have hu' : u.val.fst=h := hu
  have hunit := rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ
  have hU : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖u.val.fst x‖ ≤ (1 : ℝ≥0) := by
    rw [hu']
    exact hunit.mono (fun _ hx => by rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2)
  obtain ⟨v,hv,hgrad⟩ := sphericalSobolevGraph_bounded_product_ae D.dimension_ge_one β
    D.hamiltonian D.hamiltonian_contDiff.continuous F u CF 1 hF hU
  have hv' : v.val.fst=ᵐ[gibbsLaw N β D.hamiltonian] fun x => F.val.fst x*h x := by
    simpa only [hu'] using hv
  refine ⟨u,v,hu,hv',?_,?_⟩
  · intro ij
    simpa only [hu'] using hgrad ij
  · have hw := hweak v
    have hV : inner ℝ (killingMultiplication D β κ hκ K hK h)
        (sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous v)=
        ∫ x,κ x*F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [multiplication_ae (gibbsLaw N β D.hamiltonian) κ hκ.aestronglyMeasurable K (.of_forall hK) h,hv'] with x hx hvx
      change killingMultiplication D β κ hκ K hK h x=κ x*h x at hx
      change inner ℝ (killingMultiplication D β κ hκ K hK h x) (v.val.fst x)=_
      simp only [RCLike.inner_apply,conj_trivial,hx,hvx]
      ring
    have hL : inner ℝ h
        (sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous v)=
        ∫ x,F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv'] with x hvx
      change inner ℝ (h x) (v.val.fst x)=_
      simp only [RCLike.inner_apply,conj_trivial,hvx]
      ring
    have hR : inner ℝ (killingVector D β κ hκ)
        (sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous v)=
        ∫ x,κ x*F.val.fst x*h x ∂gibbsLaw N β D.hamiltonian := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous κ hκ,hv'] with x hx hvx
      change killingVector D β κ hκ x=κ x at hx
      change inner ℝ (killingVector D β κ hκ x) (v.val.fst x)=_
      simp only [RCLike.inner_apply,conj_trivial,hx,hvx]
      ring
    rw [hV,hL,hR] at hw
    exact hw

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
