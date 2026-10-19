-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralIntegralForm
public import SlowEquilibration.ConditionedEntranceSmoothKilledFormEquation

/-! The actual source killed resolvent equation in scalar-integral
form, for every completed Sobolev test. This makes the linear
first-commutator test available without an assumed weak equation. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm KilledOperator
set_option autoImplicit false
set_option maxHeartbeats 400000
variable {N : ℕ}

theorem rateLaplace_killing_integral_form (D : SourceData N) (β : ℝ)
    (κ : Vector N→ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0≤κ x)
    (K : ℝ≥0) (hK : ∀ x, ‖κ x‖≤K)
    (θ : ℝ≥0) (hθ : 0<θ) :
    let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
    ∃ u : sphericalSobolevGraph D.dimension_ge_one β
      D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.dimension_ge_one β D.hamiltonian
        D.hamiltonian_contDiff.continuous u=h ∧
      ∀ v : sphericalSobolevGraph D.dimension_ge_one β
        D.hamiltonian D.hamiltonian_contDiff.continuous,
        sphericalCompletedDirichlet D.dimension_ge_one β D.hamiltonian
          D.hamiltonian_contDiff.continuous u v+
          (∫ x, ((θ : ℝ)+κ x)*u.val.fst x*v.val.fst x
            ∂gibbsLaw N β D.hamiltonian)=
          ∫ x, κ x*v.val.fst x ∂gibbsLaw N β D.hamiltonian := by
  dsimp only
  let h := rateLaplace D β κ hκ hκ0 θ (killingVector D β κ hκ)
  obtain ⟨u,hu,hform⟩ :=
    rateLaplace_killing_formEquation D β κ hκ hκ0 K hK θ hθ
  refine ⟨u,hu,?_⟩
  intro v
  have hiH : Integrable (fun x => h x*v.val.fst x)
      (gibbsLaw N β D.hamiltonian) := by
    simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using
      L2.integrable_inner (𝕜:=ℝ) h v.val.fst
  have hm := multiplication_ae (gibbsLaw N β D.hamiltonian) κ
    hκ.aestronglyMeasurable K (.of_forall hK) h
  have hiC : Integrable (fun x => κ x*h x*v.val.fst x)
      (gibbsLaw N β D.hamiltonian) := by
    apply (L2.integrable_inner (𝕜:=ℝ)
      (killingMultiplication D β κ hκ K hK h) v.val.fst).congr
    filter_upwards [hm] with x hx
    change killingMultiplication D β κ hκ K hK h x=κ x*h x at hx
    simp only [RCLike.inner_apply,conj_trivial,hx]
    ring
  have hq : (∫ x, ((θ : ℝ)+κ x)*u.val.fst x*v.val.fst x
      ∂gibbsLaw N β D.hamiltonian)=
      inner ℝ (killingMultiplication D β κ hκ K hK h) v.val.fst+
      (θ : ℝ)*inner ℝ h v.val.fst := by
    rw [show u.val.fst=h from hu]
    have he : (fun x => ((θ : ℝ)+κ x)*h x*v.val.fst x)=
        fun x => κ x*h x*v.val.fst x+
          (θ : ℝ)*(h x*v.val.fst x) := funext (fun x => by ring)
    rw [he,integral_add hiC (hiH.const_mul (θ : ℝ)),integral_const_mul,
      SmoothKilledGeneral.realLp_inner_integral,
      SmoothKilledGeneral.realLp_inner_integral]
    congr 1
    apply integral_congr_ae
    exact hm.mono (fun x hx => by
      change killingMultiplication D β κ hκ K hK h x=κ x*h x at hx
      change κ x*h x*v.val.fst x=
        (killingMultiplication D β κ hκ K hK h x)*v.val.fst x
      rw [hx])
  have hf : inner ℝ (killingVector D β κ hκ) v.val.fst=
      ∫ x,κ x*v.val.fst x ∂gibbsLaw N β D.hamiltonian := by
    rw [SmoothKilledGeneral.realLp_inner_integral]
    apply integral_congr_ae
    exact (gibbsToL2_coe D.dimension_ge_one β D.hamiltonian
      D.hamiltonian_contDiff.continuous κ hκ).mono
        (fun x hx => by
          change killingVector D β κ hκ x=κ x at hx
          change killingVector D β κ hκ x*v.val.fst x=
            κ x*v.val.fst x
          rw [hx])
  rw [hq,← hf]
  have hform' := hform v
  change sphericalCompletedDirichlet D.dimension_ge_one β D.hamiltonian
      D.hamiltonian_contDiff.continuous u v+
      inner ℝ (killingMultiplication D β κ hκ K hK h) v.val.fst+
      (θ : ℝ)*inner ℝ h v.val.fst=
      inner ℝ (killingVector D β κ hκ) v.val.fst at hform'
  simpa only [add_assoc] using hform'

end SlowEquilibration.ConditionedEntrance.SmoothKilled
