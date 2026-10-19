-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralFormEquation

/-! Actual full-domain physical source equation with literal scalar
integrals, for every continuous endpoint forcing. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalModel SphericalForm KilledOperator
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem realLp_inner_integral (μ : Measure (Vector N)) (f g : Lp ℝ 2 μ) :
    inner ℝ f g=∫ x,f x*g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  exact .of_forall (fun x => by simp only [RCLike.inner_apply,conj_trivial,mul_comm])

theorem rateLaplace_continuousForcing_integral_form (D : FieldData N) (β : ℝ) (κ : Vector N→ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0≤κ x) (K : ℝ≥0) (hK : ∀ x,‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) (g : Vector N→ℝ) (hg : Continuous g) :
    let h := rateLaplace D β κ hκ hκ0 θ
      (gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous g hg)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u=h ∧
      ∀ v : sphericalSobolevGraph D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalCompletedDirichlet D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous u v+
          (∫ x,((θ : ℝ)+κ x)*u.val.fst x*v.val.fst x ∂gibbsLaw N β D.hamiltonian)=
          ∫ x,g x*v.val.fst x ∂gibbsLaw N β D.hamiltonian := by
  let f := gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous g hg
  let h := rateLaplace D β κ hκ hκ0 θ f
  obtain ⟨u,hu,hform⟩ := rateLaplace_formEquation D β κ hκ hκ0 K hK θ hθ f
  have hu' : u.val.fst=h := hu
  refine ⟨u,hu,?_⟩
  intro v
  have hiH : Integrable (fun x => h x*v.val.fst x) (gibbsLaw N β D.hamiltonian) := by
    simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using L2.integrable_inner (𝕜:=ℝ) h v.val.fst
  have hm := multiplication_ae (gibbsLaw N β D.hamiltonian) κ hκ.aestronglyMeasurable K (.of_forall hK) h
  have hiC : Integrable (fun x => κ x*h x*v.val.fst x) (gibbsLaw N β D.hamiltonian) := by
    apply (L2.integrable_inner (𝕜:=ℝ) (killingMultiplication D β κ hκ K hK h) v.val.fst).congr
    filter_upwards [hm] with x hx
    change killingMultiplication D β κ hκ K hK h x=κ x*h x at hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    ring
  have hq : (∫ x,((θ : ℝ)+κ x)*u.val.fst x*v.val.fst x ∂gibbsLaw N β D.hamiltonian)=
      inner ℝ (killingMultiplication D β κ hκ K hK h) v.val.fst+(θ : ℝ)*inner ℝ h v.val.fst := by
    rw [hu']
    have he : (fun x => ((θ : ℝ)+κ x)*h x*v.val.fst x)=
        fun x => κ x*h x*v.val.fst x+(θ : ℝ)*(h x*v.val.fst x) := funext (fun x => by ring)
    rw [he,integral_add hiC (hiH.const_mul (θ : ℝ)),integral_const_mul,
      realLp_inner_integral,realLp_inner_integral]
    congr 1
    apply integral_congr_ae
    exact hm.mono (fun x hx => by
      change killingMultiplication D β κ hκ K hK h x=κ x*h x at hx
      change κ x*h x*v.val.fst x=(killingMultiplication D β κ hκ K hK h x)*v.val.fst x
      rw [hx])
  have hf : inner ℝ f v.val.fst=∫ x,g x*v.val.fst x ∂gibbsLaw N β D.hamiltonian := by
    rw [realLp_inner_integral]
    apply integral_congr_ae
    exact (gibbsToL2_coe D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous g hg).mono
      (fun x hx => by
        change f x=g x at hx
        change f x*v.val.fst x=g x*v.val.fst x
        rw [hx])
  rw [hq,← hf]
  simpa only [add_assoc] using hform v

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
