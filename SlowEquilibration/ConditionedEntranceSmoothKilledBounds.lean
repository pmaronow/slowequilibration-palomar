-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledMassBalance
public import SlowEquilibration.ConditionedEntranceKilledPositivity

/-! The genuine smooth-source resolvent killing transform lies in [0,1].
The actual mass identity therefore yields the source estimate with
κ(1-h), without any dimension/killing-strength limit exchange. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics SphericalReversibility
open SphericalForm KilledPositivity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem operator_nonneg (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian))
    (hU : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ U x) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ operator D β κ hκ hκ0 t U x := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let := kernel_finite D β κ hκ hκ0 t
  exact kernel_operator_nonneg _ (kernel_mass_le D β κ hκ hκ0 t)
    (kernel_gibbs_subinvariant D β κ hκ hκ0 t) U hU

theorem rateLaplace_nonneg (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (θ : ℝ≥0)
    (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian))
    (hU : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ U x) :
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ rateLaplace D β κ hκ hκ0 θ U x := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  exact KilledPositivity.rateLaplace_nonneg (semigroupData D β κ hκ hκ0)
    (fun t V hV => operator_nonneg D β κ hκ hκ0 t V hV) θ U hU

theorem rateLaplace_killing_one_identity (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    (θ : ℝ) • rateLaplace D β κ hκ hκ0 θ (constantVector D β)+
      rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)=constantVector D β := by
  obtain ⟨hd,hB⟩ := generator_constant D β κ hκ K hK
  have hi := rateLaplace_identity D β κ hκ hκ0 K hK θ hθ
    ⟨constantVector D β,hd⟩
  rw [hB,map_add,map_smul] at hi
  exact hi

theorem rateLaplace_killing_unit_interval (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ h x ∧ h x ≤ 1 := by
  let W := constantVector D β
  let V := killingVector D β κ hκ
  let R := rateLaplace D β κ hκ hκ0 θ
  have hW : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ W x := by
    filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian
      D.hamiltonian_contDiff.continuous (fun _ => 1) continuous_const] with x hx
    change W x=1 at hx
    rw [hx]
    exact zero_le_one
  have hV : ∀ᵐ x ∂gibbsLaw N β D.hamiltonian,0 ≤ V x := by
    filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian
      D.hamiltonian_contDiff.continuous κ hκ] with x hx
    change V x=κ x at hx
    exact hx ▸ hκ0 x
  have hRW := rateLaplace_nonneg D β κ hκ hκ0 θ W hW
  have hRV := rateLaplace_nonneg D β κ hκ hκ0 θ V hV
  have he : (θ : ℝ) • R W+R V=W := rateLaplace_killing_one_identity D β κ hκ hκ0 K hK θ hθ
  filter_upwards [hRW,hRV,Lp.coeFn_add ((θ : ℝ) • R W) (R V),
    Lp.coeFn_smul (θ : ℝ) (R W),
    gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
      (fun _ => 1) continuous_const] with x hrw hrv ha hs h1
  have hx := congrArg (fun U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian) => U x) he
  change W x=1 at h1
  rw [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,h1] at hx
  exact ⟨hrv,by have hp := mul_nonneg θ.coe_nonneg hrw; linarith⟩

theorem rateLaplace_killing_mass_le (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    0 ≤ (∫ x,κ x*(1-h x) ∂gibbsLaw N β D.hamiltonian) ∧
      (∫ x,κ x*(1-h x) ∂gibbsLaw N β D.hamiltonian) ≤ θ := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  have hh := rateLaplace_killing_unit_interval D β κ hκ hκ0 K hK θ hθ
  have hmean : (∫ x,h x ∂gibbsLaw N β D.hamiltonian) ≤ 1 := by
    have hi := integral_mono_ae ((Lp.memLp h).integrable (by norm_num)) (integrable_const (1 : ℝ))
      (hh.mono (fun _ hx => hx.2))
    simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one] using hi
  refine ⟨integral_nonneg_of_ae (hh.mono (fun x hx => mul_nonneg (hκ0 x) (sub_nonneg.mpr hx.2))),?_⟩
  rw [rateLaplace_mass_balance D β κ hκ hκ0 K hK θ hθ]
  exact (mul_le_mul_of_nonneg_left hmean θ.coe_nonneg).trans_eq (mul_one _)

end SlowEquilibration.ConditionedEntrance.SmoothKilled
