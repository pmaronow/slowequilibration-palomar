-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.C1SphericalGraph
public import SlowEquilibration.SphericalOperator

/-! The true self-adjoint weighted spherical form generator acts as the
literal second-order Langevin differential operator on every C² test. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalForm
open MeasureTheory Set Filter SphericalModel
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem sphericalGenerator_C2 {N : ℕ} (hN : 1≤N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) :
    ∃ hdom : gibbsToL2 hN β H hH.continuous f hf.continuous ∈
        (sphericalGenerator hN β H hH.continuous).domain,
      sphericalGenerator hN β H hH.continuous
        ⟨gibbsToL2 hN β H hH.continuous f hf.continuous,hdom⟩ =
      -gibbsToL2 hN β H hH.continuous (rotationGenerator N β H f)
        (rotationGenerator_continuous β hH hf) := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  let u := C1ToGraph hN β H hH.continuous f hf1
  let k := -gibbsToL2 hN β H hH.continuous (rotationGenerator N β H f)
    (rotationGenerator_continuous β hH hf)
  have hweak : ∀ v,sphericalCompletedDirichlet hN β H hH.continuous u v =
      inner ℝ k (sphericalEnergyL2Map hN β H hH.continuous v) := by
    intro v
    have hclosed : IsClosed {v : sphericalSobolevGraph hN β H hH.continuous |
        sphericalCompletedDirichlet hN β H hH.continuous u v =
          inner ℝ k (sphericalEnergyL2Map hN β H hH.continuous v)} := by
      apply isClosed_eq
      · unfold sphericalCompletedDirichlet
        fun_prop
      · fun_prop
    refine (smoothEnergyToGraph_dense hN β H hH.continuous).induction_on v hclosed ?_
    intro q
    let hq1 : ContDiff ℝ 1 (q : Vector N → ℝ) := (smoothCore_contDiff q).of_le (by simp)
    change sphericalCompletedDirichlet hN β H hH.continuous
      (C1ToGraph hN β H hH.continuous f hf1)
      (C1ToGraph hN β H hH.continuous q hq1) =
      inner ℝ (-gibbsToL2 hN β H hH.continuous (rotationGenerator N β H f)
        (rotationGenerator_continuous β hH hf))
        (sphericalEnergyL2Map hN β H hH.continuous (C1ToGraph hN β H hH.continuous q hq1))
    rw [sphericalCompletedDirichlet_C1,C1ToGraph_L2,inner_neg_left,gibbsToL2_inner]
    have hi := rotationGenerator_integration_by_parts hN β hH hq1 hf
    rw [dirichletForm_symmetric N β H q f] at hi
    have he : (∫ x,rotationGenerator N β H f x*q.val x ∂gibbsLaw N β H)=
        ∫ x,q.val x*rotationGenerator N β H f x ∂gibbsLaw N β H :=
      integral_congr_ae (.of_forall (fun x => mul_comm _ _))
    rw [he]
    linarith only [hi]
  exact sphericalGenerator_of_weakEquation hN β H hH.continuous u k hweak

end SlowEquilibration.SphericalForm
