-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureKilledWeightedEnergy
public import SlowEquilibration.SphericalWeightedCrossAbsorption
public import SlowEquilibration.ConditionedEntrancePureReferenceBounds
public import SlowEquilibration.SphericalFisherGibbsDomination

/-! Actual killed-resolvent energy after direct Fisher absorption of the
literal completed-gradient cross term. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalModel SphericalForm KilledOperator SphericalAging.HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem rateLaplace_killing_fisher_energy (D : FieldData N) (β : ℝ) (κ : Vector N→ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0≤κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ)
    (F : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (CF : ℝ≥0) (hF : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖F.val.fst x‖≤CF)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,1≤F.val.fst x) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F/2+
        (∫ x,κ x*F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian)+
        (θ : ℝ)*(∫ x,F.val.fst x*(h x)^2 ∂gibbsLaw N β D.hamiltonian) ≤
        (∫ x,κ x*F.val.fst x ∂gibbsLaw N β D.hamiltonian)+
        sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F/2 := by
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  have hF0 : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0≤F.val.fst x :=
    hFlo.mono (fun _ hx => by linarith)
  obtain ⟨u,hu,he⟩ := rateLaplace_killing_weighted_energy D β κ hκ hκ0 K hK θ hθ F CF hF hF0
  have hu' : u.val.fst=h := hu
  have hub : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖u.val.fst x‖≤(1 : ℝ≥0) := by
    rw [hu']
    exact (rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ).mono
      (fun _ hx => by rw [Real.norm_eq_abs,abs_of_nonneg hx.1];exact hx.2)
  have hc := sphericalWeightedGradientCross_absorption D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous u F CF hub hF hFlo
  refine ⟨u,hu,?_⟩
  have hl := (abs_le.mp hc).1
  linarith



theorem rateLaplace_killing_gradient_bound (D : FieldData N) (β : ℝ) (κ : Vector N→ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0<θ)
    (F : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (CF : ℝ≥0) (hF : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,‖F.val.fst x‖ ≤ CF)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,1 ≤ F.val.fst x) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      0 ≤ sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F ∧
      sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F ≤
        2*(∫ x,κ x*F.val.fst x ∂gibbsLaw N β D.hamiltonian)+
          sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F := by
  obtain ⟨u,hu,he⟩ := rateLaplace_killing_fisher_energy D β κ hκ hκ0 K hK θ hθ F CF hF hFlo
  have hF0 : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ F.val.fst x := hFlo.mono (fun _ hx => by linarith)
  have hk : 0 ≤ ∫ x,κ x*F.val.fst x*
      (rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ) x)^2 ∂gibbsLaw N β D.hamiltonian :=
    integral_nonneg_of_ae (hF0.mono (fun x hx => mul_nonneg (mul_nonneg (hκ0 x) hx) (sq_nonneg _)))
  have ha : 0 ≤ (θ : ℝ)*(∫ x,F.val.fst x*
      (rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ) x)^2 ∂gibbsLaw N β D.hamiltonian) :=
    mul_nonneg θ.coe_nonneg (integral_nonneg_of_ae (hF0.mono (fun x hx => mul_nonneg hx (sq_nonneg _))))
  refine ⟨u,hu,sphericalWeightedGradientSquare_nonnegative D.dimension_ge_one β D.hamiltonian
    D.hamiltonian_contDiff.continuous u F hF0,?_⟩
  linarith


theorem field_reference_finite_gradient_energy (D D₀ : FieldData N)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ)
    (B : ℝ) (hB : 0 ≤ B) (hbase : ∀ x, OnSphere x → |D₀.hamiltonian x| ≤ B)
    (W : ℝ) (hW : ∀ x, OnSphere x → |β*D.hamiltonian x-β*D₀.hamiltonian x| ≤ W)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (hκ1 : ∀ x, κ x ≤ 1) :
    let C := 1+Real.exp (2*β*B)
    let H₀ := 2*Real.log 2+4*β*B
    let F := referenceRate D₀ β θ (referenceInitialVector D₀ β)
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ F₀ : sphericalSobolevGraph D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous,
      ∃ F₁ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalEnergyL2Map D.dimension_ge_one β D₀.hamiltonian D₀.hamiltonian_contDiff.continuous F₀=F ∧
        (F₁.val.fst=ᵐ[gibbsLaw N β D.hamiltonian] F) ∧
        (∀ ij : Fin N×Fin N,F₁.val.snd ij=ᵐ[gibbsLaw N β D.hamiltonian] F₀.val.snd ij) ∧
        sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
        sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F₁ ≤
          Real.exp (2*W)*(θ : ℝ)*H₀ ∧
        0 ≤ sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ ∧
        sphericalWeightedGradientSquare D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u F₁ ≤
          2*C+Real.exp (2*W)*(θ : ℝ)*H₀ := by
  dsimp only
  have hK : ∀ x,‖κ x‖ ≤ (1 : ℝ≥0) := by
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (hκ0 x)]
    exact hκ1 x
  obtain ⟨F₀,F₁,u,hF₀,hF₁,hGF₁,hu,hFb,hJF,_⟩ :=
    rateLaplace_reference_commutator_energy D D₀ β hβ κ hκ hκ0 1 hK θ hθ B hB hbase
  let C := 1+Real.exp (2*β*B)
  have hF₀val : F₀.val.fst=referenceRate D₀ β θ (referenceInitialVector D₀ β) := hF₀
  have hAC := (gibbsLaw_absolutelyContinuous_gibbsLaw D.dimension_ge_one β β D.hamiltonian
    D₀.hamiltonian D.hamiltonian_contDiff.continuous).ae_le
  have hF₀lo : ∀ᵐ x ∂gibbsLaw N β D₀.hamiltonian,1 ≤ F₀.val.fst x := by
    rw [hF₀val]
    exact ((referenceRate_field_bounds D D₀ β hβ θ hθ B hbase).filter_mono hAC).mono (fun _ hx => hx.1)
  obtain ⟨F₁',hF₁',_,hJFd⟩ := sphericalFisher_changeGibbs_le D.dimension_ge_one β β
    D₀.hamiltonian D.hamiltonian D₀.hamiltonian_contDiff.continuous
    D.hamiltonian_contDiff.continuous F₀ hF₀lo W hW
  have heF : F₁'=F₁ := sphericalSobolevGraph_eq_of_value_ae D.dimension_ge_one β D.hamiltonian
    (D.hamiltonian_contDiff.of_le (by norm_num)) F₁' F₁
    (hF₁'.trans (by simpa only [hF₀val] using hF₁.symm))
  rw [heF] at hJFd
  have hJFs : sphericalFisher D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous F₁ ≤
      Real.exp (2*W)*(θ : ℝ)*(2*Real.log 2+4*β*B) := by
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


end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
