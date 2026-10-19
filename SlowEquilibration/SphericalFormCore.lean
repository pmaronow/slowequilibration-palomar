module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalWeakResolvent
public import SlowEquilibration.SphericalGeneratorFormula

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology ContDiff

@[simp] theorem sphericalEnergyL2Map_smooth {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : smoothCore N) :
    sphericalEnergyL2Map hN β H hH (smoothEnergyToGraph hN β H hH f) =
      gibbsToL2 hN β H hH f (smoothCore_contDiff f).continuous := rfl

theorem smoothEnergyToGraph_dense {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : DenseRange (smoothEnergyToGraph hN β H hH) := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  have hm : z.val ∈ closure (Set.range (smoothGradientGraphLinear hN β H hH)) := z.property
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨f, hf⟩ := hw
  refine ⟨f, ?_⟩
  change dist z.val (smoothGradientGraphLinear hN β H hH f) < ε
  simpa only [hf] using hdist

theorem sphericalCompletedDirichlet_smooth_pairing {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f g : smoothCore N) :
    sphericalCompletedDirichlet hN β H hH
      (smoothEnergyToGraph hN β H hH f) (smoothEnergyToGraph hN β H hH g) =
      dirichletForm N β H f g := by
  have hf : ContDiff ℝ 1 (f : Vector N → ℝ) := (smoothCore_contDiff f).of_le (by simp)
  have hg : ContDiff ℝ 1 (g : Vector N → ℝ) := (smoothCore_contDiff g).of_le (by simp)
  change inner ℝ (gradientScale N • rotationGradientL2 hN β H hH f hf)
    (gradientScale N • rotationGradientL2 hN β H hH g hg) = _
  rw [real_inner_smul_left, real_inner_smul_right]
  have hir : inner ℝ (rotationGradientL2 hN β H hH f hf) (rotationGradientL2 hN β H hH g hg) =
      ∑ i : Fin N, ∑ j : Fin N, ∫ x,
        lieDerivative (coordinateRotation i j) f.val x * lieDerivative (coordinateRotation i j) g.val x
        ∂gibbsLaw N β H := by
    rw [PiLp.inner_apply]
    simp only [rotationGradientL2, WithLp.ofLp_toLp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [gibbsToL2_inner]
  rw [hir, dirichletForm_eq_rotation_integrals hN β hH hf hg]
  have hs : gradientScale N * gradientScale N = 1 / (2 * (N : ℝ)) := by
    rw [← pow_two, gradientScale, Real.sq_sqrt (by positivity)]
  rw [← mul_assoc, hs]

/-- The completed graph Hilbert norm is exactly the literal form norm. -/
theorem sphericalSobolev_norm_sq {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u : sphericalSobolevGraph hN β H hH) :
    ‖u‖ ^ 2 = ‖sphericalEnergyL2Map hN β H hH u‖ ^ 2 +
      sphericalCompletedDirichlet hN β H hH u u := by
  rw [sphericalCompletedDirichlet, real_inner_self_eq_norm_sq]
  exact WithLp.prod_norm_sq_eq_of_L2 u.val

/-- The actual right-hand side `(1-L)g`, as an actual Gibbs L² element. -/
def smoothResolventForcing {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) (g : smoothCore N) : Lp ℝ 2 (gibbsLaw N β H) :=
  gibbsToL2 hN β H hH.continuous (fun x => g.val x - rotationGenerator N β H g.val x)
    ((smoothCore_contDiff g).continuous.sub
      (rotationGenerator_continuous β hH ((smoothCore_contDiff g).of_le (by simp))))

/-- On the genuine smooth core, the actual variational resolvent agrees with
`(1-L)⁻¹`. This identifies the closed form realization with the actual
spherical differential generator on its smooth domain. -/
theorem sphericalWeakSolution_smoothForcing {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) (g : smoothCore N) :
    sphericalWeakSolution hN β H hH.continuous (smoothResolventForcing hN β H hH g) =
      smoothEnergyToGraph hN β H hH.continuous g := by
  symm
  apply sphericalWeakSolution_unique
  intro v
  have hclosed : IsClosed {v : sphericalSobolevGraph hN β H hH.continuous |
      sphericalCompletedDirichlet hN β H hH.continuous (smoothEnergyToGraph hN β H hH.continuous g) v +
      inner ℝ (sphericalEnergyL2Map hN β H hH.continuous (smoothEnergyToGraph hN β H hH.continuous g))
        (sphericalEnergyL2Map hN β H hH.continuous v) =
      inner ℝ (smoothResolventForcing hN β H hH g) (sphericalEnergyL2Map hN β H hH.continuous v)} := by
    apply isClosed_eq
    · unfold sphericalCompletedDirichlet
      fun_prop
    · fun_prop
  refine (smoothEnergyToGraph_dense hN β H hH.continuous).induction_on
    (p := fun w =>
      sphericalCompletedDirichlet hN β H hH.continuous (smoothEnergyToGraph hN β H hH.continuous g) w +
      inner ℝ (sphericalEnergyL2Map hN β H hH.continuous (smoothEnergyToGraph hN β H hH.continuous g))
        (sphericalEnergyL2Map hN β H hH.continuous w) =
      inner ℝ (smoothResolventForcing hN β H hH g) (sphericalEnergyL2Map hN β H hH.continuous w))
    v hclosed ?_
  intro f
  rw [sphericalCompletedDirichlet_smooth_pairing, sphericalEnergyL2Map_smooth,
    sphericalEnergyL2Map_smooth, gibbsToL2_inner]
  unfold smoothResolventForcing
  rw [gibbsToL2_inner]
  have hf : ContDiff ℝ 1 (f : Vector N → ℝ) := (smoothCore_contDiff f).of_le (by simp)
  have hg : ContDiff ℝ 2 (g : Vector N → ℝ) := (smoothCore_contDiff g).of_le (by simp)
  have hprod : Integrable (fun x => g.val x * f.val x) (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH.continuous
      ((smoothCore_contDiff g).continuous.mul (smoothCore_contDiff f).continuous)
  have hgen : Integrable (fun x => f.val x * rotationGenerator N β H g.val x) (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH.continuous
      ((smoothCore_contDiff f).continuous.mul (rotationGenerator_continuous β hH hg))
  have hi : (∫ x, (g.val x - rotationGenerator N β H g.val x) * f.val x ∂gibbsLaw N β H) =
      (∫ x, g.val x * f.val x ∂gibbsLaw N β H) -
      (∫ x, f.val x * rotationGenerator N β H g.val x ∂gibbsLaw N β H) := by
    rw [← integral_sub hprod hgen]
    congr 1
    funext x
    ring
  rw [hi]
  have hbp := rotationGenerator_integration_by_parts hN β hH hf hg
  rw [dirichletForm_symmetric N β H f g] at hbp
  linarith only [hbp]

/-- The actual L² resolvent acts correctly on each actual smooth test. -/
theorem sphericalL2Resolvent_smoothForcing {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 1 H) (g : smoothCore N) :
    sphericalL2Resolvent hN β H hH.continuous (smoothResolventForcing hN β H hH g) =
      gibbsToL2 hN β H hH.continuous g (smoothCore_contDiff g).continuous := by
  change sphericalEnergyL2Map hN β H hH.continuous
    (sphericalWeakSolution hN β H hH.continuous (smoothResolventForcing hN β H hH g)) = _
  rw [sphericalWeakSolution_smoothForcing, sphericalEnergyL2Map_smooth]

end
end SlowEquilibration.SphericalForm
