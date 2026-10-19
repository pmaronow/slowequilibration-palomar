-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceEquilibriumCapOccupation
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceLaplace

/-! Finite-horizon discounted smooth cap firing under the actual stationary
source Gibbs law and original Wiener process. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SlowEquilibration.SphericalModel
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance.PhysicalHitting
open SphericalAging HardSphereDynamics FeynmanKac
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- At fixed time, the product of the actual source Gibbs initial law and
original Brownian law gives the Gibbs mean of the killed expectation. -/
theorem sourceGibbsKilledExpectation_eq {N : ℕ} (D : SmoothKilled.SourceData N)
    (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ y, 0 ≤ κ y) (hκ1 : ∀ y, κ y ≤ 1) (t : ℝ≥0) :
    killedExpectation
      ((gibbsLaw N β D.hamiltonian).prod (VectorBrownian.law N)) κ
      (sourceUniformProcess D β) t κ =
      ∫ x, SmoothKilled.expectation D β κ t κ x
        ∂gibbsLaw N β D.hamiltonian := by
  let X := sourceUniformProcess D β
  let π := gibbsLaw N β D.hamiltonian
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  have hm := sourceUniformProcess_measurable D β
  have hs := survival_stronglyMeasurable κ hκ.measurable X hm t
  have hk : StronglyMeasurable (fun q : Vector N × VectorBrownian.Space N => κ (X t q)) :=
    (hκ.measurable.comp (hm.comp (measurable_const.prodMk measurable_id))).stronglyMeasurable
  have hi : Integrable (fun q => survival κ X t q * κ (X t q))
      (π.prod (VectorBrownian.law N)) := by
    apply Integrable.of_bound (hs.mul hk).aestronglyMeasurable 1
    exact .of_forall fun q => by
      change ‖survival κ X t q * κ (X t q)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (survival_nonneg κ X t q) (hκ0 _))]
      exact (mul_le_of_le_one_left (hκ0 _) (survival_le_one κ hκ0 X t q)).trans
        (hκ1 _)
  exact integral_prod _ hi

/-- Exact Fubini identity for the finite discounted firing mass when the
initial spin has the actual source Gibbs law. -/
theorem sourceGibbs_finiteDiscountedMass_expectation_eq {N : ℕ}
    (D : SmoothKilled.SourceData N) (β : ℝ)
    (κ : Vector N → ℝ) (hκ : Continuous κ)
    (hκ0 : ∀ y, 0 ≤ κ y) (hκ1 : ∀ y, κ y ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (L : ℝ≥0) :
    (∫ x, ∫ omega,
      finiteDiscountedMass κ (SmoothKilled.process D β x) θ L omega
        ∂VectorBrownian.law N ∂gibbsLaw N β D.hamiltonian) =
      ∫ t in (0 : ℝ)..(L : ℝ), Real.exp (-θ * t) *
        (∫ x, SmoothKilled.expectation D β κ t.toNNReal κ x
          ∂gibbsLaw N β D.hamiltonian) := by
  let X := sourceUniformProcess D β
  let π := gibbsLaw N β D.hamiltonian
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  have hm := sourceUniformProcess_measurable D β
  have hi : Integrable (finiteDiscountedMass κ X θ L)
      (π.prod (VectorBrownian.law N)) :=
    Integrable.of_bound
      (finiteDiscountedMass_stronglyMeasurable κ hκ.measurable X hm θ L).aestronglyMeasurable
      (L : ℝ) (.of_forall (finiteDiscountedMass_norm_le κ hκ0 hκ1 X hθ L))
  calc
    _ = ∫ q, finiteDiscountedMass κ X θ L q
        ∂(π.prod (VectorBrownian.law N)) := (integral_prod _ hi).symm
    _ = ∫ t in (0 : ℝ)..(L : ℝ), Real.exp (-θ * t) *
        killedExpectation (π.prod (VectorBrownian.law N)) κ X t.toNNReal κ :=
      finiteDiscountedMass_expectation_eq _ κ hκ.measurable hκ0 hκ1 X hm hθ L
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change Real.exp (-θ * t) * killedExpectation
        (π.prod (VectorBrownian.law N)) κ (sourceUniformProcess D β) t.toNNReal κ = _
      rw [sourceGibbsKilledExpectation_eq D β κ hκ hκ0 hκ1]

/-- From an actual source Gibbs initial spin and original Brownian noise,
finite discounted physical cap firing is at most the horizon times the
initial source Gibbs cap mass. -/
theorem sourceGibbs_capKilling_finiteDiscountedMass_mean_le
    {N : ℕ} (D : SmoothKilled.SourceData N) (β : ℝ)
    {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : 0 ≤ θ) (L : ℝ≥0) :
    (∫ x, ∫ omega,
      finiteDiscountedMass (capKilling α D.axis) (SmoothKilled.process D β x)
        θ L omega ∂VectorBrownian.law N
        ∂gibbsLaw N β D.hamiltonian) ≤
      (L : ℝ) * (∫ x, capKilling α D.axis x
        ∂gibbsLaw N β D.hamiltonian) := by
  let κ := capKilling α D.axis
  let π := gibbsLaw N β D.hamiltonian
  let K := ∫ x, κ x ∂π
  have hκ : Continuous κ := (capKilling_contDiff α D.axis).continuous
  have hκ0 : ∀ y, 0 ≤ κ y := capKilling_nonneg α D.axis
  have hκ1 : ∀ y, κ y ≤ 1 := capKilling_le_one hα D.axis
  let : IsProbabilityMeasure π :=
    gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  have he0 (t : ℝ≥0) (x : Vector N) :
      0 ≤ SmoothKilled.expectation D β κ t κ x := by
    change 0 ≤ ∫ omega,
      survival κ (SmoothKilled.process D β x) t omega *
        κ (SmoothKilled.process D β x t omega) ∂VectorBrownian.law N
    exact integral_nonneg (fun omega => mul_nonneg
      (survival_nonneg κ (SmoothKilled.process D β x) t omega) (hκ0 _))
  have hmean0 (t : ℝ) :
      0 ≤ ∫ x, SmoothKilled.expectation D β κ t.toNNReal κ x ∂π :=
    integral_nonneg (he0 t.toNNReal)
  have hpoint (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) (L : ℝ)) :
      Real.exp (-θ * t) *
        (∫ x, SmoothKilled.expectation D β κ t.toNNReal κ x ∂π) ≤ K := by
    have hdiscount : Real.exp (-θ * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    exact (mul_le_of_le_one_left (hmean0 t) hdiscount).trans
      (sourceGibbs_capKilling_expectation_mean_le D β hα t.toNNReal)
  rw [sourceGibbs_finiteDiscountedMass_expectation_eq D β κ hκ hκ0 hκ1 hθ L,
    intervalIntegral.integral_of_le L.coe_nonneg]
  have hmono :
      (∫ t in Ioc (0 : ℝ) (L : ℝ), Real.exp (-θ * t) *
        (∫ x, SmoothKilled.expectation D β κ t.toNNReal κ x ∂π)) ≤
      ∫ _t in Ioc (0 : ℝ) (L : ℝ), K := by
    apply integral_mono_of_nonneg
    · exact .of_forall fun t => mul_nonneg (Real.exp_nonneg _) (hmean0 t)
    · exact integrable_const _
    · exact (ae_restrict_iff' measurableSet_Ioc).2
        (.of_forall fun t ht => hpoint t ht)
  have hvol : (volume.restrict (Ioc (0 : ℝ) (L : ℝ))).real Set.univ = (L : ℝ) := by
    simp [Measure.real, Real.volume_Ioc]
  exact hmono.trans (by simpa only [K,κ,π,integral_const,smul_eq_mul,hvol]
    using (le_refl ((L : ℝ) * K)))

end SlowEquilibration.ConditionedEntrance.PhysicalHitting
