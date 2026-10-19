-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSobolevGibbsTransport
public import SlowEquilibration.SphericalGibbsTiltIdentity
public import SlowEquilibration.SphericalCompletedGradientIntegral
public import SlowEquilibration.SphericalGeneratorDomainForm

/-! The actual full-domain spherical weak commutator between two continuous
Gibbs Hamiltonians, derived from actual domain transport and reference
integration by parts. No weak commutator or form compatibility is assumed. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped InnerProductSpace BigOperators
namespace SlowEquilibration.SphericalForm
open SphericalModel ConditionedEntrance
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

/-- Every actual reference-generator element and completed test can be
transported to the actual tilted Gibbs form, with the exact weak
commutator and literal completed rotation-gradient integral. -/
theorem sphericalGenerator_gibbs_weak_commutator (hN : 1 ≤ N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N → ℝ) (hH₀ : Continuous H₀) (hH₁ : Continuous H₁)
    (U : (sphericalGenerator hN β₀ H₀ hH₀).domain)
    (v : sphericalSobolevGraph hN β₀ H₀ hH₀) :
    let w := gibbsEnergyDifference β₀ β₁ H₀ H₁
    ∃ u : sphericalSobolevGraph hN β₀ H₀ hH₀,
      ∃ u₁ v₁ : sphericalSobolevGraph hN β₁ H₁ hH₁,
        sphericalEnergyL2Map hN β₀ H₀ hH₀ u=U.val ∧
        (u₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] U.val) ∧
        (v₁.val.fst=ᵐ[gibbsLaw N β₁ H₁] v.val.fst) ∧
        sphericalCompletedDirichlet hN β₁ H₁ hH₁ u₁ v₁=
          (∫ x,Real.exp (-w x)*(sphericalGenerator hN β₀ H₀ hH₀ U x)*v₁.val.fst x
            ∂gibbsLaw N β₁ H₁)+
          ∫ x,tiltDefect w x*completedGradientPairing hN β₀ H₀ hH₀ u v x ∂gibbsLaw N β₁ H₁ := by
  let w := gibbsEnergyDifference β₀ β₁ H₀ H₁
  have hw : Continuous w := (hH₁.const_mul β₁).sub (hH₀.const_mul β₀)
  let M := partition N β₁ H₁/partition N β₀ H₀
  have hM : 0 < M := div_pos (partition_pos hN β₁ hH₁) (partition_pos hN β₀ hH₀)
  obtain ⟨u,hu,hform⟩ := sphericalGenerator_domain_form hN β₀ H₀ hH₀ U
  have hu' : u.val.fst=U.val := hu
  obtain ⟨u₁,hu₁,hGu₁⟩ := sphericalSobolevGraph_changeGibbs hN β₀ β₁ H₀ H₁ hH₀ hH₁ u
  obtain ⟨v₁,hv₁,hGv₁⟩ := sphericalSobolevGraph_changeGibbs hN β₀ β₁ H₀ H₁ hH₀ hH₁ v
  have hΓ : Integrable (completedGradientPairing hN β₀ H₀ hH₀ u v) (gibbsLaw N β₀ H₀) :=
    completedGradientPairing_integrable hN β₀ H₀ hH₀ u v
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt N)).exists_bound_of_continuousOn (Real.continuous_exp.comp hw).continuousOn
  have hb : ∀ᵐ x ∂gibbsLaw N β₀ H₀,‖Real.exp (w x)‖ ≤ C :=
    ((sphereLaw_mem_closedBall hN).filter_mono (gibbsLaw_absolutelyContinuous β₀ H₀).ae_le).mono (fun x hx => hC x hx)
  have heΓ := hΓ.bdd_mul (Real.continuous_exp.comp hw).aestronglyMeasurable hb
  have hIBP : (∫ x,(sphericalGenerator hN β₀ H₀ hH₀ U x)*v.val.fst x ∂gibbsLaw N β₀ H₀)=
      ∫ x,completedGradientPairing hN β₀ H₀ hH₀ u v x ∂gibbsLaw N β₀ H₀ := by
    have hi := hform v
    rw [sphericalCompletedDirichlet_integral,L2.inner_def] at hi
    apply Eq.trans _ hi.symm
    apply integral_congr_ae
    exact .of_forall (fun x => by
      change (sphericalGenerator hN β₀ H₀ hH₀ U x)*v.val.fst x=
        inner ℝ (sphericalGenerator hN β₀ H₀ hH₀ U x) (v.val.fst x)
      simp only [RCLike.inner_apply,conj_trivial,mul_comm])
  have hcomm := exponential_tilt_weak_commutator (gibbsLaw N β₀ H₀) w hw.measurable hM
    (completedGradientPairing hN β₀ H₀ hH₀ u v)
    (fun x => (sphericalGenerator hN β₀ H₀ hH₀ U x)*v.val.fst x) hΓ heΓ hIBP
  rw [← gibbsLaw_normalizedTilt hN β₀ β₁ H₀ H₁ hH₀ hH₁] at hcomm
  have hGu : ∀ᵐ x ∂gibbsLaw N β₁ H₁,∀ ij : Fin N × Fin N,u₁.val.snd ij x=u.val.snd ij x :=
    ae_all_iff.mpr hGu₁
  have hGv : ∀ᵐ x ∂gibbsLaw N β₁ H₁,∀ ij : Fin N × Fin N,v₁.val.snd ij x=v.val.snd ij x :=
    ae_all_iff.mpr hGv₁
  have hΓeq : completedGradientPairing hN β₁ H₁ hH₁ u₁ v₁=ᵐ[gibbsLaw N β₁ H₁]
      completedGradientPairing hN β₀ H₀ hH₀ u v := by
    filter_upwards [hGu,hGv] with x hux hvx
    simp only [completedGradientPairing]
    apply Finset.sum_congr rfl
    intro ij _
    rw [hux ij,hvx ij]
  have hl : sphericalCompletedDirichlet hN β₁ H₁ hH₁ u₁ v₁=
      ∫ x,completedGradientPairing hN β₀ H₀ hH₀ u v x ∂gibbsLaw N β₁ H₁ :=
    (sphericalCompletedDirichlet_integral hN β₁ H₁ hH₁ u₁ v₁).trans (integral_congr_ae hΓeq)
  have hr : (∫ x,(1-tiltDefect w x)*((sphericalGenerator hN β₀ H₀ hH₀ U x)*v.val.fst x)
      ∂gibbsLaw N β₁ H₁)=
      ∫ x,Real.exp (-w x)*(sphericalGenerator hN β₀ H₀ hH₀ U x)*v₁.val.fst x ∂gibbsLaw N β₁ H₁ := by
    apply integral_congr_ae
    filter_upwards [hv₁] with x hx
    simp only [tiltDefect,sub_sub_cancel,hx]
    ring
  refine ⟨u,u₁,v₁,hu,?_,hv₁,?_⟩
  · simpa only [hu'] using hu₁
  · rw [hl,hcomm,hr]

end SlowEquilibration.SphericalForm
