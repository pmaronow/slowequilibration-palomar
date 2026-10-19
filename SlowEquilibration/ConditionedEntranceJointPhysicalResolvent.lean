-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledIntegralForm
public import SlowEquilibration.SphericalJointResolventVariational
public import SlowEquilibration.SphericalWeightedChangeGibbs
public import SlowEquilibration.SphericalSobolevGibbsTransport

/-! Identification of the common measurable variational family with the
literal physical source resolvent. The actual full weak equation is
derived from the physical inverse before applying common-domain uniqueness. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ} {Θ : Type*} [TopologicalSpace Θ]

theorem jointResolventSolution_actual_source (D : SourceData N) (β : ℝ)
    (θ : ℝ≥0) (hθ : 0<θ) (H κ g : Θ×Vector N→ℝ)
    (hH : Continuous H) (hκ : Continuous κ) (hg : Continuous g) (hκ0 : ∀ z,0≤κ z)
    (p : Θ) (hHp : ∀ x,H (p,x)=D.hamiltonian x)
    (K : ℝ≥0) (hK : ∀ x,‖κ (p,x)‖≤K) :
    let κp := fun x => κ (p,x)
    let hκp := hκ.comp (continuous_const.prodMk continuous_id)
    let gp := fun x => g (p,x)
    let hgp := hg.comp (continuous_const.prodMk continuous_id)
    let h := rateLaplace D β κp hκp (fun x => hκ0 (p,x)) θ
      (gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous gp hgp)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      ((jointResolventSolution D.dimension_ge_one β (θ : ℝ) H κ g hH hκ hg p).val.fst=ᵐ[gibbsLaw N 0 (fun _ => 0)] h) ∧
      ∀ ij : Fin N×Fin N,
        (jointResolventSolution D.dimension_ge_one β (θ : ℝ) H κ g hH hκ hg p).val.snd ij=ᵐ[gibbsLaw N 0 (fun _ => 0)] u.val.snd ij := by
  let κp := fun x => κ (p,x)
  let gp := fun x => g (p,x)
  have hκp : Continuous κp := hκ.comp (continuous_const.prodMk continuous_id)
  have hgp : Continuous gp := hg.comp (continuous_const.prodMk continuous_id)
  have hκp0 : ∀ x,0≤κp x := fun x => hκ0 (p,x)
  let h := rateLaplace D β κp hκp hκp0 θ
    (gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous gp hgp)
  obtain ⟨u,hu,hform⟩ := rateLaplace_continuousForcing_integral_form D β κp hκp hκp0 K hK θ hθ gp hgp
  have hu' : u.val.fst=h := hu
  obtain ⟨u₀,hu₀,hGu₀⟩ := sphericalSobolevGraph_changeGibbs D.dimension_ge_one β 0
    D.hamiltonian (fun _ => 0) D.hamiltonian_contDiff.continuous continuous_const u
  have hAC := gibbsLaw_absolutelyContinuous_zeroHamiltonian β D.hamiltonian
  have hU : u.val.fst=ᵐ[gibbsLaw N β D.hamiltonian] u₀.val.fst := (hAC.ae_eq hu₀).symm
  have hGU (ij : Fin N×Fin N) : u.val.snd ij=ᵐ[gibbsLaw N β D.hamiltonian] u₀.val.snd ij :=
    (hAC.ae_eq (hGu₀ ij)).symm
  have hθr : 0<(θ : ℝ) := by exact_mod_cast hθ
  obtain ⟨c,hc,hρc,hσc⟩ := jointKilledCoefficients_positive D.dimension_ge_one β (θ : ℝ) hθr H κ hH hκ hκ0 p
  have hρ : jointKilledRho β H hH p=ᵐ[gibbsLaw N 0 (fun _ => 0)]
      fun x => Real.exp (gibbsEnergyDifference 0 β (fun _ => 0) D.hamiltonian x) := by
    filter_upwards [jointKilledRho_ae D.dimension_ge_one β H hH p] with x hx
    rw [hx,hHp]
    simp only [gibbsEnergyDifference,zero_mul,sub_zero]
  have hσ : jointKilledSigma β (θ : ℝ) H κ hH hκ p=ᵐ[gibbsLaw N 0 (fun _ => 0)]
      fun x => ((θ : ℝ)+κp x)*Real.exp (gibbsEnergyDifference 0 β (fun _ => 0) D.hamiltonian x) := by
    filter_upwards [jointKilledSigma_ae D.dimension_ge_one β (θ : ℝ) H κ hH hκ p] with x hx
    rw [hx,hHp]
    simp only [gibbsEnergyDifference,zero_mul,sub_zero,κp]
  let M := partition N β D.hamiltonian/partition N 0 (fun _ => 0)
  have heq : u₀=jointResolventSolution D.dimension_ge_one β (θ : ℝ) H κ g hH hκ hg p := by
    apply sphericalWeightedSolution_unique D.dimension_ge_one 0 (fun _ => 0) continuous_const
      (jointKilledRho β H hH p) (jointKilledSigma β (θ : ℝ) H κ hH hκ p) c hc hρc hσc
      (jointKilledForcing β H g hH hg p)
    intro v₀
    obtain ⟨v₁,hv₁,hGv₁⟩ := sphericalSobolevGraph_changeGibbs D.dimension_ge_one 0 β
      (fun _ => 0) D.hamiltonian continuous_const D.hamiltonian_contDiff.continuous v₀
    have he := sphericalWeightedOperator_changeGibbs D.dimension_ge_one 0 β (fun _ => 0) D.hamiltonian
      continuous_const D.hamiltonian_contDiff.continuous _ _ (fun x => (θ : ℝ)+κp x)
      hρ hσ u₀ v₀ u v₁ hU hv₁ hGU hGv₁
    have hf : inner ℝ (jointKilledForcing β H g hH hg p) v₀.val.fst=
        M*(∫ x,gp x*v₁.val.fst x ∂gibbsLaw N β D.hamiltonian) := by
      rw [realLp_inner_integral]
      calc
        _ = ∫ x,Real.exp (gibbsEnergyDifference 0 β (fun _ => 0) D.hamiltonian x)*
            (gp x*v₀.val.fst x) ∂gibbsLaw N 0 (fun _ => 0) := by
          apply integral_congr_ae
          filter_upwards [jointKilledForcing_ae D.dimension_ge_one β H g hH hg p] with x hx
          rw [hx,hHp]
          simp only [gibbsEnergyDifference,zero_mul,sub_zero]
          ring
        _ = M*(∫ x,gp x*v₀.val.fst x ∂gibbsLaw N β D.hamiltonian) :=
          integral_exp_changeGibbs D.dimension_ge_one 0 β (fun _ => 0) D.hamiltonian
            continuous_const D.hamiltonian_contDiff.continuous _
        _ = M*(∫ x,gp x*v₁.val.fst x ∂gibbsLaw N β D.hamiltonian) := by
          congr 1
          apply integral_congr_ae
          exact hv₁.mono (fun x hx => by
            change gp x*v₀.val.fst x=gp x*v₁.val.fst x
            rw [hx])
    exact he.trans ((congrArg (fun t : ℝ => M*t) (hform v₁)).trans hf.symm)
  refine ⟨u,hu,?_,?_⟩
  · rw [← heq]
    simpa only [hu'] using hu₀
  · intro ij
    rw [← heq]
    exact hGu₀ ij

end SlowEquilibration.ConditionedEntrance.SmoothKilled
