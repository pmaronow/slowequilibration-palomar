-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.UniformSmoothApproximation
public import SlowEquilibration.SphericalWeakResolvent

@[expose] public section

namespace SlowEquilibration.SphericalForm

open MeasureTheory MeasureTheory.Measure Filter Metric Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped Topology InnerProductSpace ContDiff

theorem gibbsToL2_sub {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (f g : Vector N → ℝ) (hf : Continuous f) (hg : Continuous g) :
    gibbsToL2 hN β H hH (f-g) (hf.sub hg) =
      gibbsToL2 hN β H hH f hf - gibbsToL2 hN β H hH g hg := rfl

/-- An actual almost-everywhere uniform representative bound controls the
ordinary Gibbs L² distance, using the proved probability normalization. -/
theorem gibbsToL2_dist_le_of_ae_bound {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f g : Vector N → ℝ)
    (hf : Continuous f) (hg : Continuous g) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂gibbsLaw N β H, dist (f x) (g x) ≤ C) :
    dist (gibbsToL2 hN β H hH f hf) (gibbsToL2 hN β H hH g hg) ≤ C := by
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  have hi := integrable_gibbs_of_continuous hN β hH ((hf.sub hg).pow 2)
  have hb : ∀ᵐ x ∂gibbsLaw N β H, (f x-g x)^2 ≤ C^2 := by
    filter_upwards [hbound] with x hx
    have hh : |f x-g x| ≤ C := by simpa only [Real.dist_eq] using hx
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr hh
  have hsq := integral_mono_ae hi (integrable_const (C^2)) hb
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul, Pi.pow_apply, Pi.sub_apply] at hsq
  have hn : ‖gibbsToL2 hN β H hH f hf - gibbsToL2 hN β H hH g hg‖^2 =
      ∫ x, (f x-g x)^2 ∂gibbsLaw N β H := by
    rw [← gibbsToL2_sub hN β H hH f g hf hg, ← real_inner_self_eq_norm_sq,
      gibbsToL2_inner]
    simp only [Pi.sub_apply, pow_two]
  rw [← hn] at hsq
  rw [dist_eq_norm]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mp hsq

/-- Shrinking almost-everywhere representative bounds give genuine Gibbs L²
convergence. This lemma is applied to values and actual rotation derivatives. -/
theorem gibbsToL2_tendsto_of_ae_bound {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : ℕ → Vector N → ℝ) (g : Vector N → ℝ)
    (hf : ∀ n, Continuous (f n)) (hg : Continuous g) (C : ℕ → ℝ)
    (hC : ∀ n, 0 ≤ C n) (ht : Tendsto C atTop (𝓝 (0:ℝ)))
    (hbound : ∀ n, ∀ᵐ x ∂gibbsLaw N β H, dist (f n x) (g x) ≤ C n) :
    Tendsto (fun n => gibbsToL2 hN β H hH (f n) (hf n)) atTop
      (𝓝 (gibbsToL2 hN β H hH g hg)) := by
  apply tendsto_const_nhds.congr_dist
  apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_) ht
  rw [dist_comm]
  exact gibbsToL2_dist_le_of_ae_bound hN β H hH (f n) g (hf n) hg (hC n) (hbound n)

/-- Uniform control of genuine Frechet derivatives controls every actual
rotation derivative on the Gibbs sphere. -/
theorem lieDerivative_dist_bound_onSphere {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (A : Operator N) (f g : Vector N → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, dist (fderiv ℝ f x) (fderiv ℝ g x) ≤ C) :
    ∀ᵐ x ∂gibbsLaw N β H,
      dist (lieDerivative A f x) (lieDerivative A g x) ≤ C*(‖A‖*((N:ℝ)+1)) := by
  filter_upwards [gibbsLaw_support hN β H] with x hx
  have hxnorm : ‖x‖ ≤ (N:ℝ)+1 := by
    nlinarith [norm_nonneg x, Nat.cast_nonneg (α := ℝ) N]
  have hder : ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ C := by
    simpa only [dist_eq_norm] using hbound x
  rw [dist_eq_norm]
  change ‖(fderiv ℝ f x-fderiv ℝ g x) (A x)‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ f x-fderiv ℝ g x‖ * ‖A x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C*(‖A‖*‖x‖) := mul_le_mul hder (A.le_opNorm x) (norm_nonneg _) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxnorm (norm_nonneg A)) hC

/-- Every actual compact-supported C¹ ambient function belongs to the
genuine spherical smooth-gradient graph closure. Its value and gradient are
approximated by the actual normalized-bump convolutions. -/
theorem compact_C1_mem_sphericalSobolevGraph {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    WithLp.toLp 2 (gibbsToL2 hN β H hH f hf.continuous,
      normalizedRotationGradientL2 hN β H hH f hf) ∈ sphericalSobolevGraph hN β H hH := by
  obtain ⟨g, hg, hv, hd⟩ := UniformSmoothApproximation.exists_uniform_smooth_C1_sequence
    (volume : Measure (Vector N)) f hf hcf
  have hε : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hval := gibbsToL2_tendsto_of_ae_bound hN β H hH g f (fun n => (hg n).continuous)
    hf.continuous (fun n => 1/((n:ℝ)+1)) (fun n => by positivity) hε
    (fun n => ae_of_all _ (hv n))
  have hpi : Tendsto (fun (n : ℕ) (ij : Fin N × Fin N) =>
      gibbsToL2 hN β H hH (lieDerivative (coordinateRotation ij.1 ij.2) (g n))
        (lieDerivative_continuous _ ((hg n).of_le (by simp)))) atTop
      (𝓝 (fun ij : Fin N × Fin N =>
        gibbsToL2 hN β H hH (lieDerivative (coordinateRotation ij.1 ij.2) f)
          (lieDerivative_continuous _ hf))) := by
    apply tendsto_pi_nhds.mpr
    intro ij
    let A := coordinateRotation ij.1 ij.2
    have ht := hε.mul_const (‖A‖*((N:ℝ)+1))
    simp only [zero_mul] at ht
    exact gibbsToL2_tendsto_of_ae_bound hN β H hH
      (fun n => lieDerivative A (g n)) (lieDerivative A f)
      (fun n => lieDerivative_continuous _ ((hg n).of_le (by simp)))
      (lieDerivative_continuous _ hf)
      (fun n => (1/((n:ℝ)+1))*(‖A‖*((N:ℝ)+1))) (fun n => by positivity) ht
      (fun n => lieDerivative_dist_bound_onSphere hN β H A (g n) f (by positivity) (hd n))
  have hrot : Tendsto (fun n => rotationGradientL2 hN β H hH (g n) ((hg n).of_le (by simp)))
      atTop (𝓝 (rotationGradientL2 hN β H hH f hf)) :=
    ((PiLp.homeomorph 2 (fun _ : Fin N × Fin N => Lp ℝ 2 (gibbsLaw N β H))).symm.continuous.tendsto _).comp hpi
  have hgrad := hrot.const_smul (gradientScale N)
  change Tendsto (fun n => normalizedRotationGradientL2 hN β H hH (g n) ((hg n).of_le (by simp)))
    atTop (𝓝 (normalizedRotationGradientL2 hN β H hH f hf)) at hgrad
  have hprod := hval.prodMk_nhds hgrad
  have hgraph : Tendsto (fun n => smoothGradientGraphLinear hN β H hH ⟨g n, hg n⟩) atTop
      (𝓝 (WithLp.toLp 2 (gibbsToL2 hN β H hH f hf.continuous,
        normalizedRotationGradientL2 hN β H hH f hf))) :=
    ((WithLp.homeomorphProd 2 _ _).symm.continuous.tendsto _).comp hprod
  have hclosed : IsClosed (sphericalSobolevGraph hN β H hH).carrier := by
    change IsClosed (LinearMap.range (smoothGradientGraphLinear hN β H hH)).topologicalClosure.carrier
    exact Submodule.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hgraph
  exact Eventually.of_forall (fun n => (smoothEnergyToGraph hN β H hH ⟨g n, hg n⟩).property)

/-- Every actual C¹ ambient function, without a support restriction, belongs
to the spherical Sobolev graph. A smooth compact cutoff is one near the true
Gibbs sphere, so both its actual value and Frechet derivative agree there. -/
theorem C1_mem_sphericalSobolevGraph {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    WithLp.toLp 2 (gibbsToL2 hN β H hH f hf.continuous,
      normalizedRotationGradientL2 hN β H hH f hf) ∈ sphericalSobolevGraph hN β H hH := by
  let r : ℝ := (N:ℝ)+1
  have hr : 0 < r := by dsimp [r]; positivity
  let φ : ContDiffBump (0 : Vector N) := ⟨r, r+1, hr, by linarith⟩
  let g : Vector N → ℝ := fun x => φ x*f x
  have hg : ContDiff ℝ 1 g := φ.contDiff.mul hf
  have hcg : HasCompactSupport g := φ.hasCompactSupport.mul_right
  have hnear : ∀ᵐ x ∂gibbsLaw N β H, g =ᶠ[𝓝 x] f := by
    filter_upwards [gibbsLaw_support hN β H] with x hx
    have hxnorm : ‖x‖ < r := by
      dsimp [r]
      nlinarith [norm_nonneg x, Nat.cast_nonneg (α := ℝ) N]
    have hxball : x ∈ ball (0 : Vector N) φ.rIn := by
      simpa only [mem_ball, dist_zero_right] using hxnorm
    have hφ := φ.eventuallyEq_one_of_mem_ball hxball
    exact hφ.mono (fun y hy => by dsimp [g]; rw [hy]; simp only [Pi.one_apply, one_mul])
  have hval : gibbsToL2 hN β H hH g hg.continuous =
      gibbsToL2 hN β H hH f hf.continuous :=
    gibbsToL2_congr hN β H hH g f hg.continuous hf.continuous
      (hnear.mono (fun x hx => hx.eq_of_nhds))
  have hrot : rotationGradientL2 hN β H hH g hg = rotationGradientL2 hN β H hH f hf := by
    apply PiLp.ext
    intro ij
    change gibbsToL2 hN β H hH (lieDerivative (coordinateRotation ij.1 ij.2) g)
      (lieDerivative_continuous _ hg) =
      gibbsToL2 hN β H hH (lieDerivative (coordinateRotation ij.1 ij.2) f)
        (lieDerivative_continuous _ hf)
    apply gibbsToL2_congr
    filter_upwards [hnear] with x hx
    unfold lieDerivative
    rw [hx.fderiv_eq]
  have hgrad : normalizedRotationGradientL2 hN β H hH g hg =
      normalizedRotationGradientL2 hN β H hH f hf := by
    unfold normalizedRotationGradientL2
    rw [hrot]
  have hmem := compact_C1_mem_sphericalSobolevGraph hN β H hH g hg hcg
  rw [hval, hgrad] at hmem
  exact hmem

/-- The actual closed-form graph representative of an ambient C¹ function.
Membership is proved by ordinary smooth mollification, not assumed. -/
noncomputable def C1ToGraph {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    sphericalSobolevGraph hN β H hH :=
  ⟨WithLp.toLp 2 (gibbsToL2 hN β H hH f hf.continuous,
    normalizedRotationGradientL2 hN β H hH f hf), C1_mem_sphericalSobolevGraph hN β H hH f hf⟩

theorem C1ToGraph_L2 {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    sphericalEnergyL2Map hN β H hH (C1ToGraph hN β H hH f hf) =
      gibbsToL2 hN β H hH f hf.continuous := rfl

theorem C1ToGraph_gradient {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    sphericalEnergyGradientMap hN β H hH (C1ToGraph hN β H hH f hf) =
      normalizedRotationGradientL2 hN β H hH f hf := rfl

/-- The actual completed bilinear form agrees with the true spherical
Dirichlet pairing on any two C¹ ambient functions. -/
theorem sphericalCompletedDirichlet_C1 {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f g : Vector N → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    sphericalCompletedDirichlet hN β H hH (C1ToGraph hN β H hH f hf)
      (C1ToGraph hN β H hH g hg) = dirichletForm N β H f g := by
  change inner ℝ (normalizedRotationGradientL2 hN β H hH f hf)
    (normalizedRotationGradientL2 hN β H hH g hg) = _
  simp only [normalizedRotationGradientL2, inner_smul_left_eq_smul,
    inner_smul_right, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, gradientScale, Real.sq_sqrt (by positivity),
    dirichletForm_eq_rotation_integrals hN β hH hf hg]
  congr 1
  rw [PiLp.inner_apply]
  simp only [rotationGradientL2, WithLp.ofLp_toLp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [gibbsToL2_inner]

/-- The genuine completed form agrees with the actual gradient energy on
every C¹ ambient function. -/
theorem sphericalCompletedDirichlet_C1_energy {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : ContDiff ℝ 1 f) :
    sphericalCompletedDirichlet hN β H hH (C1ToGraph hN β H hH f hf)
      (C1ToGraph hN β H hH f hf) = dirichletEnergy N β H f := by
  change inner ℝ (normalizedRotationGradientL2 hN β H hH f hf)
    (normalizedRotationGradientL2 hN β H hH f hf) = _
  rw [real_inner_self_eq_norm_sq, dirichletEnergy_eq_normalizedRotationGradientL2_norm]

end SlowEquilibration.SphericalForm
