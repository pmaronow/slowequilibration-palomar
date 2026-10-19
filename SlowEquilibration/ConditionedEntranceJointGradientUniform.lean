-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointReducedEnergy
public import SlowEquilibration.ConditionedEntranceSourceFiniteGradientEnergy

/-! The uniform physical source gradient estimate applies to the same
jointly measurable representatives used in the weighted-energy reduction.
This supplies a finite axis-integrable envelope for the raw gradient energy. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
open SphericalAging.HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_joint_weighted_gradient_uniform_bound
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ)
    (p : SourceParameters N μ) (hp : OnSphere p.2.1)
    (hJ : p.1 ∈ regularDisorder)
    (hbar kbar B R : ℝ)
    (hh : |p.2.2.1| ≤ hbar) (hk : |p.2.2.2| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s, |χ s| ≤ B) (hχR : ∀ s, R < |s| → χ s = 0)
    (F : SourceParameters N μ × Vector N → ℝ)
    (G : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ)
    (u : sphericalSobolevGraph hN β
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian_contDiff.continuous)
    (hF : (fun x => F (p,x)) =ᵐ[gibbsLaw N β
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian]
      referenceRate (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).baseData
        β θ (referenceInitialVector
          (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).baseData β))
    (hu : sphericalEnergyL2Map hN β
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian
      (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian_contDiff.continuous u =
      rateLaplace (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp)
        β (PhysicalHitting.capKilling α p.2.1)
        (PhysicalHitting.capKilling_contDiff α p.2.1).continuous
        (PhysicalHitting.capKilling_nonneg α p.2.1) θ
        (killingVector (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp)
          β (PhysicalHitting.capKilling α p.2.1)
          (PhysicalHitting.capKilling_contDiff α p.2.1).continuous))
    (hG : ∀ ij : Fin N × Fin N,
      (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β
        (SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp).hamiltonian]
        u.val.snd ij) :
    let W := β * PhysicalHitting.uniformCutoffEnergyConstant μ Q hbar kbar B R *
      (N : ℝ) * α ^ μ.minDegree
    let C := 1 + Real.exp (2 * β * derivativeConstant (mixtureCoefficients μ) * (N : ℝ))
    let H₀ := 2 * Real.log 2 + 4 * β * derivativeConstant (mixtureCoefficients μ) * (N : ℝ)
    let H := sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ
    0 ≤ jointGibbsWeightedGradientSquare β H F G p ∧
    jointGibbsWeightedGradientSquare β H F G p ≤
      2 * C + Real.exp (2 * W) * (θ : ℝ) * H₀ := by
  dsimp only
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hp
  obtain ⟨F₀,F₁,u',hF₀,hF₁,hGF₁,hu',hJF,hB0,hBu⟩ :=
    SmoothKilled.source_reference_finite_gradient_energy D β hβ θ hθ hJ
      hbar kbar B R hh hk hB hR hχB hχR
  have heu : u' = u := sphericalEnergyL2Map_injective hN β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) (hu'.trans hu.symm)
  rw [heu] at hB0 hBu
  have hFEq : (fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian] F₁.val.fst :=
    hF.trans hF₁.symm
  have hHEq (x : Vector N) :
      sourceJointHamiltonian μ Q hQ hnp α χ (p,x) = D.hamiltonian x := rfl
  have hBEq : jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian μ Q hQ hnp α χ) F G p =
      sphericalWeightedGradientSquare hN β D.hamiltonian
        D.hamiltonian_contDiff.continuous u F₁ := by
    unfold jointGibbsWeightedGradientSquare sphericalWeightedGradientSquare
    simp only [hHEq]
    apply Finset.sum_congr rfl
    intro ij _
    apply integral_congr_ae
    filter_upwards [hFEq, hG ij] with x hx hg
    rw [hx,hg]
  exact ⟨hBEq.symm ▸ hB0, hBEq.trans_le hBu⟩

/-- The actual joint weighted gradient square is axis-integrable for the
physical graph representatives. The bound is uniform over the spherical
axis once the disorder, marks and cutoff are fixed. -/
theorem source_joint_weighted_gradient_axis_integrable
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (hnp : μ.minDegree < μ.maxDegree) (Q : ℝ) (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (α : ℝ) (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ)
    (J : Disorder N μ.maxDegree) (hJ : J ∈ regularDisorder)
    (e k hbar kbar B R : ℝ)
    (hh : |e| ≤ hbar) (hk : |k| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hχB : ∀ s, |χ s| ≤ B) (hχR : ∀ s, R < |s| → χ s = 0)
    (F : SourceParameters N μ × Vector N → ℝ)
    (G : (Fin N × Fin N) → SourceParameters N μ × Vector N → ℝ)
    (hBm : Measurable (jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ) F G))
    (hphys : ∀ v : Vector N, ∀ hv : OnSphere v,
      let p : SourceParameters N μ := (J,(v,(e,k)))
      let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ p hv
      ∃ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
        (fun x => F (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian]
          referenceRate D.baseData β θ (referenceInitialVector D.baseData β) ∧
        sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u =
          rateLaplace D β (PhysicalHitting.capKilling α v)
            (PhysicalHitting.capKilling_contDiff α v).continuous
            (PhysicalHitting.capKilling_nonneg α v) θ
            (killingVector D β (PhysicalHitting.capKilling α v)
              (PhysicalHitting.capKilling_contDiff α v).continuous) ∧
        ∀ ij : Fin N × Fin N,
          (fun x => G ij (p,x)) =ᵐ[gibbsLaw N β D.hamiltonian] u.val.snd ij) :
    Integrable (fun v => jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ) F G (J,(v,(e,k))))
      (sphereLaw N) := by
  let W := β * PhysicalHitting.uniformCutoffEnergyConstant μ Q hbar kbar B R *
    (N : ℝ) * α ^ μ.minDegree
  let C := 1 + Real.exp (2 * β * derivativeConstant (mixtureCoefficients μ) * (N : ℝ))
  let H₀ := 2 * Real.log 2 + 4 * β * derivativeConstant (mixtureCoefficients μ) * (N : ℝ)
  let L := 2 * C + Real.exp (2 * W) * (θ : ℝ) * H₀
  have hmeas : Measurable (fun v => jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ) F G (J,(v,(e,k)))) :=
    hBm.comp (show Measurable (fun v : Vector N =>
      ((J,(v,(e,k))) : SourceParameters N μ)) by fun_prop)
  apply Integrable.of_bound hmeas.aestronglyMeasurable L
  filter_upwards [sphereLaw_support hN] with v hv
  have hv' : OnSphere v := (onSphere_iff_norm_sq v).mpr hv
  obtain ⟨u,hF,hu,hG⟩ := hphys v hv'
  have hb := source_joint_weighted_gradient_uniform_bound hN μ hnp Q hQ hQ1
    α hα χ hχ β hβ θ hθ (J,(v,(e,k))) hv' hJ
    hbar kbar B R hh hk hB hR hχB hχR F G u hF hu hG
  change 0 ≤ jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian μ Q hQ hnp α χ) F G (J,(v,(e,k))) ∧
    jointGibbsWeightedGradientSquare β
      (sourceJointHamiltonian μ Q hQ hnp α χ) F G (J,(v,(e,k))) ≤ L at hb
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

end SlowEquilibration.ConditionedEntrance
