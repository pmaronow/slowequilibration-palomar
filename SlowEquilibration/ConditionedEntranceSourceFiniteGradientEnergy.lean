-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGradientBound
public import SlowEquilibration.ConditionedEntranceSmoothKilledCommutatorEnergy
public import SlowEquilibration.ConditionedEntranceSourceReferenceBounds
public import SlowEquilibration.ConditionedEntrancePhysicalCutoffEnergy
public import SlowEquilibration.SphericalFisherGibbsDomination

/-! A finite actual source energy envelope on the original regular bank,
uniform in original disorder, physical axis and bounded marks. The Gibbs
oscillation factor is used solely to justify subsequent integration. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem source_reference_finite_gradient_energy (D : SourceData N) (β : ℝ) (hβ : 0 ≤ β)
    (θ : ℝ≥0) (hθ : 0<θ) (hJ : D.disorder∈regularDisorder)
    (hbar kbar B R : ℝ) (hh : |D.energyMark| ≤ hbar) (hk : |D.radialMark| ≤ kbar)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hχB : ∀ s,|D.cutoff s| ≤ B) (hχR : ∀ s,R < |s| → D.cutoff s=0) :
    let W := β*PhysicalHitting.uniformCutoffEnergyConstant D.mixture D.Q hbar kbar B R*
      (N : ℝ)*D.cutoffScale^D.mixture.minDegree
    let C := 1+Real.exp (2*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ))
    let H₀ := 2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)
    let κ := PhysicalHitting.capKilling D.cutoffScale D.axis
    let hκ := (PhysicalHitting.capKilling_contDiff D.cutoffScale D.axis).continuous
    let hκ0 := PhysicalHitting.capKilling_nonneg D.cutoffScale D.axis
    let F := referenceRate D.baseData β θ (referenceInitialVector D.baseData β)
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ F₀ : sphericalSobolevGraph D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
      ∃ F₁ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalEnergyL2Map D.dimension_ge_one β D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀=F ∧
        (F₁.val.fst=ᵐ[gibbsLaw N β D.hamiltonian] F) ∧
        (∀ ij : Fin N×Fin N,F₁.val.snd ij=ᵐ[gibbsLaw N β D.hamiltonian] F₀.val.snd ij) ∧
        sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
        sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F₁ ≤
          Real.exp (2*W)*(θ : ℝ)*H₀ ∧
        0 ≤ sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ ∧
        sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ ≤
          2*C+Real.exp (2*W)*(θ : ℝ)*H₀ := by
  dsimp only
  let κ := PhysicalHitting.capKilling D.cutoffScale D.axis
  have hκ := (PhysicalHitting.capKilling_contDiff D.cutoffScale D.axis).continuous
  have hκ0 := PhysicalHitting.capKilling_nonneg D.cutoffScale D.axis
  have hκ1 := PhysicalHitting.capKilling_le_one D.cutoffScale_pos D.axis
  have hK : ∀ x,‖κ x‖ ≤ (1 : ℝ≥0) := by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (hκ0 x)]
    exact hκ1 x
  obtain ⟨F₀,F₁,u,hF₀,hF₁,hGF₁,hu,hFb,hJF,_⟩ :=
    rateLaplace_reference_commutator_energy D β hβ κ hκ hκ0 1 hK θ hθ hJ
  let C := 1+Real.exp (2*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ))
  let W := β*PhysicalHitting.uniformCutoffEnergyConstant D.mixture D.Q hbar kbar B R*
    (N : ℝ)*D.cutoffScale^D.mixture.minDegree
  have hF₀val : F₀.val.fst=referenceRate D.baseData β θ (referenceInitialVector D.baseData β) := hF₀
  have hAC := (gibbsLaw_absolutelyContinuous_gibbsLaw D.dimension_ge_one β β D.hamiltonian
    D.baseData.hamiltonian D.hamiltonian_contDiff.continuous).ae_le
  have hF₀lo : ∀ᵐ x ∂gibbsLaw N β D.baseData.hamiltonian,1 ≤ F₀.val.fst x := by
    rw [hF₀val]
    exact ((referenceRate_source_regular_bounds D β hβ θ hθ hJ).filter_mono hAC).mono (fun _ hx => hx.1)
  have hW : ∀ x,OnSphere x → |β*D.hamiltonian x-β*D.baseData.hamiltonian x| ≤ W := by
    intro x hx
    rw [← mul_sub,abs_mul,abs_of_nonneg hβ,SourceData.baseData_hamiltonian]
    have hb := PhysicalHitting.regular_source_cutoff_energy_difference_uniform_marks D hJ x hx hh hk hB hR hχB hχR
    simpa only [W,mul_assoc] using mul_le_mul_of_nonneg_left hb hβ
  obtain ⟨F₁',hF₁',_,hJFd⟩ := sphericalFisher_changeGibbs_le D.dimension_ge_one β β
    D.baseData.hamiltonian D.hamiltonian D.baseData.hamiltonian_contDiff.continuous
    D.hamiltonian_contDiff.continuous F₀ hF₀lo W hW
  have heF : F₁'=F₁ := sphericalSobolevGraph_eq_of_value_ae D.dimension_ge_one β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) F₁' F₁
    (hF₁'.trans (by simpa only [hF₀val] using hF₁.symm))
  rw [heF] at hJFd
  have hJFs : sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F₁ ≤
      Real.exp (2*W)*(θ : ℝ)*(2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients D.mixture)*(N : ℝ)) := by
    exact hJFd.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hJF (Real.exp_pos _).le)
  let CF : ℝ≥0 := ⟨C,by positivity⟩
  obtain ⟨u',hu',hB0,hBu⟩ := rateLaplace_killing_gradient_bound D β κ hκ hκ0 1 hK θ hθ F₁ CF
    (hFb.mono (fun _ hx => hx.2)) (hFb.mono (fun _ hx => hx.1))
  have heu : u'=u := sphericalEnergyL2Map_injective D.dimension_ge_one β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) (hu'.trans hu.symm)
  rw [heu] at hB0 hBu
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  have hRn : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖κ x*F₁.val.fst x‖ ≤ C := by
    filter_upwards [hFb] with x hx
    rw [norm_mul]
    exact (mul_le_mul (hK x) hx.2 (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  have hRi : Integrable (fun x => κ x*F₁.val.fst x) (gibbsLaw N β D.hamiltonian) :=
    Integrable.of_bound (hκ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F₁.val.fst)) C hRn
  have hRb : (∫ x,κ x*F₁.val.fst x ∂gibbsLaw N β D.hamiltonian) ≤ C := by
    have hle : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,κ x*F₁.val.fst x ≤ C :=
      hRn.mono (fun x hx => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx))
    have hi := integral_mono_ae hRi (integrable_const C) hle
    simpa only [integral_const,probReal_univ,one_smul] using hi
  refine ⟨F₀,F₁,u,hF₀,hF₁,hGF₁,hu,hJFs,hB0,?_⟩
  linarith

end SlowEquilibration.ConditionedEntrance.SmoothKilled
