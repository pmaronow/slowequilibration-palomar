-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledResolventRate
public import SlowEquilibration.SphericalEigenvalues

/-! The literal integrated killing balance for the actual physical
resolvent: `∫ κ(1-h) dπ = θ ∫ h dπ`. In particular, for `κ=nχ`,
the factor n multiplies `χ(1-h)`, with no exchange of dimension and
killing-strength limits. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalForm SphericalReversibility SphericalReversibility.Ito KilledOperator
open SphericalSmoothTensorStationarity FeynmanKac
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

private theorem perturbation_core_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) (V : E →L[ℝ] E)
    (x : A.domain) (hA : A x=0) : boundedPerturbation A V x=V x := by
  rw [boundedPerturbation_apply,hA,zero_add]

def killingVector (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous κ hκ

def constantVector (D : SourceData N) (β : ℝ) : Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
    (fun _ => 1) continuous_const

theorem generator_constant (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) :
    ∃ hd : constantVector D β ∈ (generator D β κ hκ K hK).domain,
      generator D β κ hκ K hK ⟨constantVector D β,hd⟩=
        killingVector D β κ hκ := by
  let H := D.hamiltonian
  let hH := D.hamiltonian_contDiff.continuous
  obtain ⟨ha,hAa⟩ := sphericalGenerator_C2 D.dimension_ge_one β H
    (D.hamiltonian_contDiff.of_le (by norm_num)) (fun _ => 1) contDiff_const
  refine ⟨ha,?_⟩
  have hz : gibbsToL2 D.dimension_ge_one β H hH (rotationGenerator N β H (fun _ => 1))
      (rotationGenerator_continuous β (D.hamiltonian_contDiff.of_le (by norm_num)) contDiff_const)=0 := by
    apply Lp.ext
    filter_upwards [gibbsToL2_coe D.dimension_ge_one β H hH (rotationGenerator N β H (fun _ => 1))
      (rotationGenerator_continuous β (D.hamiltonian_contDiff.of_le (by norm_num)) contDiff_const),
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gibbsLaw N β H)] with x hx h0
    rw [hx]
    simp only [Pi.zero_apply] at h0
    simpa only [rotationGenerator_const] using h0.symm
  have hA0 : sphericalGenerator D.dimension_ge_one β H hH ⟨constantVector D β,ha⟩=0 :=
    hAa.trans (by rw [hz,neg_zero])
  have hB := perturbation_core_zero (E := Lp ℝ 2 (gibbsLaw N β D.hamiltonian))
    (sphericalGenerator D.dimension_ge_one β H hH) (killingMultiplication D β κ hκ K hK)
    ⟨constantVector D β,ha⟩ hA0
  apply hB.trans
  apply Lp.ext
  filter_upwards [multiplication_ae (gibbsLaw N β D.hamiltonian) κ hκ.aestronglyMeasurable K (.of_forall hK)
      (constantVector D β),
    gibbsToL2_coe D.dimension_ge_one β H hH (fun _ => 1) continuous_const,
    gibbsToL2_coe D.dimension_ge_one β H hH κ hκ] with x hm h1 hκx
  change killingMultiplication D β κ hκ K hK (constantVector D β) x=
    killingVector D β κ hκ x
  change killingMultiplication D β κ hκ K hK (constantVector D β) x=
    κ x*constantVector D β x at hm
  change constantVector D β x=1 at h1
  change killingVector D β κ hκ x=κ x at hκx
  simp only [hm,h1,hκx,mul_one]

/-- Exact physical killing balance, derived by testing the genuine
two-sided resolvent against the actual constant core vector. -/
theorem rateLaplace_mass_balance (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    (∫ x,κ x*(1-h x) ∂gibbsLaw N β D.hamiltonian)=
      (θ : ℝ)*(∫ x,h x ∂gibbsLaw N β D.hamiltonian) := by
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  let one := constantVector D β
  let V := killingVector D β κ hκ
  let B := generator D β κ hκ K hK
  have hh : h∈B.domain := rateLaplace_mem_domain D β κ hκ hκ0 K hK θ hθ V
  obtain ⟨h1,hB1⟩ := generator_constant D β κ hκ K hK
  have hformal : B.IsFormalAdjoint B := by
    have hadj := (generator_selfAdjoint D β κ hκ K hK)
    have hf := LinearPMap.adjoint_isFormalAdjoint (T := B) hadj.dense_domain
    rwa [show B.adjoint=B from hadj] at hf
  have hR := rateLaplace_resolvent D β κ hκ hκ0 K hK θ hθ V
  have hp := congrArg (fun U => inner ℝ U one) hR
  change inner ℝ ((θ : ℝ) • h+B ⟨h,hh⟩) one=inner ℝ V one at hp
  rw [inner_add_left,real_inner_smul_left,hformal ⟨h,hh⟩ ⟨one,h1⟩,hB1] at hp
  have hmean : inner ℝ h one=∫ x,h x ∂gibbsLaw N β D.hamiltonian := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
      (fun _ => 1) continuous_const] with x hx
    change one x=1 at hx
    simp only [RCLike.inner_apply,conj_trivial,hx,one_mul]
  have hmass : (∫ x,κ x*(1-h x) ∂gibbsLaw N β D.hamiltonian)=inner ℝ V (one-h) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub one h,
      gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
        (fun _ => 1) continuous_const,
      gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous κ hκ]
      with x hsub h1x hκx
    change one x=1 at h1x
    change V x=κ x at hκx
    simp only [RCLike.inner_apply,conj_trivial,hsub,Pi.sub_apply,h1x,hκx]
    ring
  change (∫ x,κ x*(1-h x) ∂gibbsLaw N β D.hamiltonian)=(θ : ℝ)*(∫ x,h x ∂gibbsLaw N β D.hamiltonian)
  rw [hmass,inner_sub_right,← hmean]
  change (θ : ℝ)*inner ℝ h one+inner ℝ h V=inner ℝ V one at hp
  have hc : inner ℝ V h=inner ℝ h V := real_inner_comm _ _
  linarith

end SlowEquilibration.ConditionedEntrance.SmoothKilled
