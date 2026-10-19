-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralL2Generator
public import SlowEquilibration.ConditionedEntranceKilledMultiplication
public import SlowEquilibration.ConditionedEntranceKilledResolventMaximality

/-! Physical source smooth-cutoff bounded-killing Feynman--Kac identification at Laplace
parameter one: the literal Brownian occupation-weighted Hilbert Laplace
integral is the true two-sided inverse of `1 + A + κ`. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalForm SphericalReversibility SphericalReversibility.Ito KilledOperator
open SphericalSmoothTensorStationarity FeynmanKac
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

private theorem perturbation_neg_core {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) (V : E →L[ℝ] E)
    (x : A.domain) (a b : E) (hA : A x=-a) (hV : V x=b) :
    -(boundedPerturbation A V) x=a-b := by
  rw [boundedPerturbation_apply,hA,hV]
  abel

def killingMultiplication (D : FieldData N) (β : ℝ)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) →L[ℝ] Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  multiplication (gibbsLaw N β D.hamiltonian) κ hκ.aestronglyMeasurable K (.of_forall hK)

def generator (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) →ₗ.[ℝ] Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  boundedPerturbation
    (sphericalGenerator D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)
    (killingMultiplication D β κ hκ K hK)

theorem generator_selfAdjoint (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) :
    IsSelfAdjoint (generator D β κ hκ K hK) :=
  boundedPerturbation_selfAdjoint _ (sphericalGenerator_selfAdjoint D.dimension_ge_one β
    D.hamiltonian D.hamiltonian_contDiff.continuous) _
    (multiplication_isSymmetric _ _ _ _ _)

theorem generator_C2_hasCore (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) :
    (generator D β κ hκ K hK).HasCore
      (LinearMap.range (c2ValueLinear D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous)) :=
  boundedPerturbation_hasCore _ (sphericalGenerator_selfAdjoint D.dimension_ge_one β
    D.hamiltonian D.hamiltonian_contDiff.continuous) _
    (multiplication_isSymmetric _ _ _ _ _) _ (sphericalGenerator_C2_hasCore D.dimension_ge_one β
      D.hamiltonian D.hamiltonian_contDiff)

theorem generator_C2_physical_derivative (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ hd : gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous f hf.continuous ∈
        (generator D β κ hκ K hK).domain,
      HasDerivWithinAt
        (fun r : ℝ => operator D β κ hκ hκ0 r.toNNReal
          (gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous f hf.continuous))
        (-(generator D β κ hκ K hK)
          ⟨gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous f hf.continuous,hd⟩)
        (Ici 0) 0 := by
  let H := D.hamiltonian
  let hH := D.hamiltonian_contDiff.continuous
  let U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian) := gibbsToL2 D.dimension_ge_one β H hH f hf.continuous
  obtain ⟨ha,hAa⟩ := sphericalGenerator_C2 D.dimension_ge_one β H (D.hamiltonian_contDiff.of_le (by norm_num)) f hf
  refine ⟨ha,?_⟩
  have hmult : killingMultiplication D β κ hκ K hK U =
      gibbsToL2 D.dimension_ge_one β H hH (fun x => κ x*f x) (hκ.mul hf.continuous) := by
    apply Lp.ext
    filter_upwards [multiplication_ae (gibbsLaw N β D.hamiltonian) κ hκ.aestronglyMeasurable K (.of_forall hK) U,
      gibbsToL2_coe D.dimension_ge_one β H hH f hf.continuous,
      gibbsToL2_coe D.dimension_ge_one β H hH (fun x => κ x*f x) (hκ.mul hf.continuous)] with x hm hu hmf
    change killingMultiplication D β κ hκ K hK U x = κ x*U x at hm
    change U x=f x at hu
    rw [hm,hu,hmf]
  have hvalue : -(generator D β κ hκ K hK) ⟨U,ha⟩ =
      generatorVector D β κ hκ f hf := by
    let a : Lp ℝ 2 (gibbsLaw N β D.hamiltonian) := gibbsToL2 D.dimension_ge_one β H hH
      (rotationGenerator N β H f)
      (rotationGenerator_continuous β (D.hamiltonian_contDiff.of_le (by norm_num)) hf)
    let b : Lp ℝ 2 (gibbsLaw N β D.hamiltonian) := gibbsToL2 D.dimension_ge_one β H hH
      (fun x => κ x*f x) (hκ.mul hf.continuous)
    have hc := perturbation_neg_core (E := Lp ℝ 2 (gibbsLaw N β D.hamiltonian))
      (sphericalGenerator D.dimension_ge_one β H hH) (killingMultiplication D β κ hκ K hK)
      ⟨U,ha⟩ a b hAa hmult
    apply hc.trans
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub a b,
      gibbsToL2_coe D.dimension_ge_one β H hH (rotationGenerator N β H f)
        (rotationGenerator_continuous β (D.hamiltonian_contDiff.of_le (by norm_num)) hf),
      gibbsToL2_coe D.dimension_ge_one β H hH (fun x => κ x*f x) (hκ.mul hf.continuous),
      gibbsToL2_coe D.dimension_ge_one β H hH
        (fun x => coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f x-κ x*f x)
        ((SphericalC1Dynamics.Ito.generator_continuous β _
          (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) hf).sub (hκ.mul hf.continuous)),
      gibbsLaw_support D.dimension_ge_one β H] with x hsub ha hb hv hx
    have he : coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f x =
        rotationGenerator N β H f x :=
      (rotationGenerator_eq_coefficientGenerator (by have := D.dimension_ge_one; omega)
        β H hf x ((onSphere_iff_norm_sq x).mpr hx)).symm
    rw [hsub,Pi.sub_apply]
    change a x-b x=generatorVector D β κ hκ f hf x
    change a x=rotationGenerator N β H f x at ha
    change b x=κ x*f x at hb
    change generatorVector D β κ hκ f hf x=
      coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f x-κ x*f x at hv
    rw [ha,hb,hv]
    exact congrArg (fun z => z-κ x*f x) he.symm
  exact (operator_C2_hasDerivWithinAt_zero D β κ hκ hκ0 K K.coe_nonneg hK f hf).congr_deriv hvalue.symm

/-- The true physical Hilbert Laplace transform is a left inverse on the
whole actual killed-generator domain, obtained by the proved C² core. -/
theorem laplace_identity (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (x : (generator D β κ hκ K hK).domain) :
    (semigroupData D β κ hκ hκ0).operator
      ((x : Lp ℝ 2 (gibbsLaw N β D.hamiltonian))+generator D β κ hκ K hK x) = x := by
  apply SemigroupLaplace.Data.operator_add_generator _ _
    (generator_selfAdjoint D β κ hκ K hK).isClosed _
    (generator_C2_hasCore D β κ hκ K hK)
  rintro ⟨_,f,rfl⟩
  exact (generator_C2_physical_derivative D β κ hκ hκ0 K hK
    f (c2Functions_contDiff f)).choose_spec

def shiftedGenerator (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) :
    Lp ℝ 2 (gibbsLaw N β D.hamiltonian) →ₗ.[ℝ] Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  boundedPerturbation (generator D β κ hκ K hK) (ContinuousLinearMap.id ℝ _)

theorem shiftedGenerator_selfAdjoint (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K) :
    IsSelfAdjoint (shiftedGenerator D β κ hκ K hK) :=
  boundedPerturbation_selfAdjoint _ (generator_selfAdjoint D β κ hκ K hK) _ (by intro x y; rfl)

theorem laplace_leftInverse (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (x : (shiftedGenerator D β κ hκ K hK).domain) :
    (semigroupData D β κ hκ hκ0).operator
      (shiftedGenerator D β κ hκ K hK x) = x := by
  change (semigroupData D β κ hκ hκ0).operator
    (generator D β κ hκ K hK x+(x : Lp ℝ 2 (gibbsLaw N β D.hamiltonian))) = x
  rw [add_comm]
  exact laplace_identity D β κ hκ hκ0 K hK x

theorem laplace_mem_domain (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (f : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    (semigroupData D β κ hκ hκ0).operator f ∈
      (generator D β κ hκ K hK).domain :=
  leftInverse_domain _ (shiftedGenerator_selfAdjoint D β κ hκ K hK) _
    (laplace_leftInverse D β κ hκ hκ0 K hK) f

/-- Genuine physical bounded-killing resolvent identification. -/
theorem laplace_resolvent (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ≥0) (hK : ∀ x, ‖κ x‖ ≤ K)
    (f : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    (semigroupData D β κ hκ hκ0).operator f+
      generator D β κ hκ K hK
        ⟨(semigroupData D β κ hκ hκ0).operator f,
          laplace_mem_domain D β κ hκ hκ0 K hK f⟩ = f := by
  have h := leftInverse_rightInverse _ (shiftedGenerator_selfAdjoint D β κ hκ K hK) _
    (laplace_leftInverse D β κ hκ hκ0 K hK) f
  change generator D β κ hκ K hK
    ⟨(semigroupData D β κ hκ hκ0).operator f,_⟩+
      (semigroupData D β κ hκ hκ0).operator f = f at h
  exact (add_comm _ _).trans h

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
