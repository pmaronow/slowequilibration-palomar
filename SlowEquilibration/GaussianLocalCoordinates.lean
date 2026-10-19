-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianKacRice
public import SlowEquilibration.GaussianRegressionIsometry
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Genuine local coefficient coordinates for every surjective observation

The invertible coefficient block is constructed from the observation's actual
kernel and orthogonal complement. Its persistence on a spatial neighborhood
comes from the openness of invertible continuous linear maps.
-/

@[expose] public section

namespace SlowEquilibration.GaussianLocalCoordinates

open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.GaussianRegression
open scoped RealInnerProductSpace ENNReal Topology

noncomputable section

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

/-- Actual orthogonal coefficient splitting, with the observed coordinates
identified by a true isometry and every kernel coordinate retained. -/
def coefficientSplit (A : E →L[ℝ] U) (hA : Surjective A) :
    WithLp 2 (U × A.ker) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2 (effectiveIsometry A hA)
    (LinearIsometryEquiv.refl ℝ A.ker)).trans
      ((LinearIsometryEquiv.withLpProdComm 2 ℝ A.kerᗮ A.ker).trans A.ker.orthogonalDecomposition.symm)

@[simp] theorem coefficientSplit_apply (A : E →L[ℝ] U) (hA : Surjective A)
    (z : WithLp 2 (U × A.ker)) :
    coefficientSplit A hA z = (z.ofLp.2 : E) + (effectiveIsometry A hA z.ofLp.1 : E) := by
  rfl

/-- Fixed observed-coordinate inclusion at the chosen base observation. -/
def firstInclusion (A : E →L[ℝ] U) (hA : Surjective A) : U →L[ℝ] E :=
  A.kerᗮ.subtypeL.comp (effectiveIsometry A hA : U →L[ℝ] A.kerᗮ)

/-- First observation block after the genuine orthogonal coefficient split. -/
def firstBlock (Gamma : U → E →L[ℝ] U) (u0 : U) (hA : Surjective (Gamma u0))
    (u : U) : U →L[ℝ] U := (Gamma u).comp (firstInclusion (Gamma u0) hA)

/-- Every remaining coefficient lies in the actual base observation kernel. -/
def secondBlock (Gamma : U → E →L[ℝ] U) (u0 : U) (u : U) : (Gamma u0).ker →L[ℝ] U :=
  (Gamma u).comp (Gamma u0).ker.subtypeL

/-- The local split observation is exactly the original full-coefficient observation. -/
theorem observationAt_eq_comp_split (Gamma : U → E →L[ℝ] U) (u0 : U)
    (hA : Surjective (Gamma u0)) (u : U) :
    GaussianKacRice.observationAt (firstBlock Gamma u0 hA) (secondBlock Gamma u0) u =
      (Gamma u).comp (coefficientSplit (Gamma u0) hA : WithLp 2 (U × (Gamma u0).ker) →L[ℝ] E) := by
  apply ContinuousLinearMap.ext
  intro z
  change Gamma u (effectiveIsometry (Gamma u0) hA z.ofLp.1 : E) +
    Gamma u (z.ofLp.2 : E) = Gamma u (coefficientSplit (Gamma u0) hA z)
  rw [coefficientSplit_apply, map_add, add_comm]

/-- Surjectivity constructs an actual invertible first block at the base point. -/
theorem firstBlock_base_invertible (Gamma : U → E →L[ℝ] U) (u0 : U)
    (hA : Surjective (Gamma u0)) : (firstBlock Gamma u0 hA u0).IsInvertible := by
  refine ⟨squareObservation (Gamma u0) hA, ?_⟩
  ext w
  rfl

/-- C1 observations remain C1 after the fixed genuine coefficient split. -/
theorem firstBlock_contDiffOn (Gamma : U → E →L[ℝ] U) (u0 : U)
    (hA : Surjective (Gamma u0)) (s : Set U) (hG : ContDiffOn ℝ 1 Gamma s) :
    ContDiffOn ℝ 1 (firstBlock Gamma u0 hA) s := hG.clm_comp contDiffOn_const

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] in
theorem secondBlock_contDiffOn (Gamma : U → E →L[ℝ] U) (u0 : U)
    (s : Set U) (hG : ContDiffOn ℝ 1 Gamma s) :
    ContDiffOn ℝ 1 (secondBlock Gamma u0) s := hG.clm_comp contDiffOn_const

/-- The invertible coefficient block persists on a true open neighborhood.
No fixed block nondegeneracy is assumed beyond actual observation surjectivity. -/
theorem exists_invertible_block_neighborhood (Gamma : U → E →L[ℝ] U)
    (s : Set U) (hs : IsOpen s) (hG : ContDiffOn ℝ 1 Gamma s)
    (u0 : U) (hu0 : u0 ∈ s) (hA : Surjective (Gamma u0)) :
    ∃ v : Set U, IsOpen v ∧ u0 ∈ v ∧ v ⊆ s ∧
      ∀ u ∈ v, (firstBlock Gamma u0 hA u).IsInvertible := by
  have hc := (firstBlock_contDiffOn Gamma u0 hA s hG).continuousOn
  have hopen : IsOpen (s ∩ (firstBlock Gamma u0 hA) ⁻¹' {T | T.IsInvertible}) :=
    hc.isOpen_inter_preimage hs ContinuousLinearMap.isOpen_setOfPred_isInvertible
  exact ⟨_, hopen, ⟨hu0, firstBlock_base_invertible Gamma u0 hA⟩,
    inter_subset_left, fun u hu => hu.2⟩

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace U] [BorelSpace U]

/-- Genuine zero count over the full ordinary observation field. -/
def zeroCount (Gamma : U → E →L[ℝ] U) (s : Set U)
    (psi : E → U → ℝ≥0∞) (z : E) : ℝ≥0∞ :=
  ∑' u : {u : U | u ∈ s ∧ Gamma u z = 0}, psi z u

/-- Actual spatial Frechet derivative at fixed coefficients. -/
def spatialJacobian (Gamma : U → E →L[ℝ] U) (z : E) (u : U) : U →L[ℝ] U :=
  fderiv ℝ (fun y => Gamma y z) u

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] [BorelSpace U] in
/-- The actual derivative-weighted conditional mark is Borel at every C1 point. -/
lemma spatial_mark_measurable (Gamma : U → E →L[ℝ] U) (u : U)
    (hG : DifferentiableAt ℝ Gamma u) (psi : E → U → ℝ≥0∞)
    (hpsi : Measurable fun p : E × U => psi p.1 p.2) :
    Measurable (fun z => ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u) := by
  have he (z : E) : spatialJacobian Gamma z u = (fderiv ℝ Gamma u).flip z := by
    simpa only [spatialJacobian, ContinuousLinearMap.comp_zero, zero_add] using
      (hG.hasFDerivAt.clm_apply (hasFDerivAt_const z u)).fderiv
  have hc : Continuous (fun z => spatialJacobian Gamma z u) := by
    simp_rw [he]
    exact (fderiv ℝ Gamma u).flip.continuous
  exact (ContinuousLinearMap.continuous_det.comp hc).abs.measurable.ennreal_ofReal.mul
    (hpsi.comp (measurable_id.prodMk measurable_const))

/-- Actual whole-coefficient Kac--Rice on a constructed local block domain.
The only block hypothesis is ordinary invertibility in that domain; the block
itself is derived from the true surjective base observation. -/
theorem local_whole_coefficients_kacRice
    (Gamma : U → E →L[ℝ] U) (u0 : U) (hA : Surjective (Gamma u0))
    (s : Set U) (hs : IsOpen s) (hG : ContDiffOn ℝ 1 Gamma s)
    (hblock : ∀ u ∈ s, (firstBlock Gamma u0 hA u).IsInvertible)
    (psi : E → U → ℝ≥0∞) (hpsi : Measurable fun p : E × U => psi p.1 p.2) :
    (∫⁻ z, zeroCount Gamma s psi z ∂stdGaussian E) =
      ∫⁻ u in s, observationPdf (Gamma u) 0 *
        ∫⁻ z, ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u
          ∂regressionKernel (Gamma u) 0 := by
  let j := coefficientSplit (Gamma u0) hA
  let G1 := firstBlock Gamma u0 hA
  let G2 := secondBlock Gamma u0
  let phi : (U × (Gamma u0).ker) → U → ℝ≥0∞ :=
    fun z u => psi (j (WithLp.toLp 2 z)) u
  have hm : Measurable fun p : (U × (Gamma u0).ker) × U => phi p.1 p.2 := by
    exact hpsi.comp ((j.continuous.measurable.comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ U (Gamma u0).ker).symm.continuous.measurable).comp
        measurable_fst |>.prodMk measurable_snd)
  have hgrad (z : WithLp 2 (U × (Gamma u0).ker)) :
      CoefficientKacRice.gradient G1 G2 z.ofLp = fun u => Gamma u (j z) := by
    funext u
    exact congrArg (fun T : WithLp 2 (U × (Gamma u0).ker) →L[ℝ] U => T z)
      (observationAt_eq_comp_split Gamma u0 hA u)
  have hcount (z : WithLp 2 (U × (Gamma u0).ker)) :
      CoefficientKacRice.gradientCount G1 G2 s phi z.ofLp = zeroCount Gamma s psi (j z) := by
    unfold CoefficientKacRice.gradientCount zeroCount
    rw [hgrad]
  have hH (z : WithLp 2 (U × (Gamma u0).ker)) (u : U) :
      CoefficientKacRice.coordinateHessian G1 G2 z.ofLp u = spatialJacobian Gamma (j z) u := by
    unfold CoefficientKacRice.coordinateHessian spatialJacobian
    rw [hgrad]
  have hlocal := GaussianKacRice.local_marked_kacRice G1 G2 s hs
    (firstBlock_contDiffOn Gamma u0 hA s hG) (secondBlock_contDiffOn Gamma u0 s hG) hblock phi hm
  have hleft : (∫⁻ z, zeroCount Gamma s psi z ∂stdGaussian E) =
      ∫⁻ z, CoefficientKacRice.gradientCount G1 G2 s phi z ∂GaussianKacRice.splitGaussian := by
    rw [← stdGaussian_map j]
    have hJ := lintegral_map_equiv (zeroCount Gamma s psi) j.toMeasurableEquiv
      (μ := stdGaussian (WithLp 2 (U × (Gamma u0).ker)))
    rw [LinearIsometryEquiv.coe_toMeasurableEquiv] at hJ
    rw [hJ]
    unfold GaussianKacRice.splitGaussian
    have hP := lintegral_map_equiv (CoefficientKacRice.gradientCount G1 G2 s phi)
      (MeasurableEquiv.toLp 2 (U × (Gamma u0).ker)).symm
      (μ := stdGaussian (WithLp 2 (U × (Gamma u0).ker)))
    change (∫⁻ z, CoefficientKacRice.gradientCount G1 G2 s phi z ∂Measure.map WithLp.ofLp _) = _ at hP
    rw [hP]
    exact lintegral_congr (fun z => (hcount z).symm)
  rw [hleft, hlocal]
  apply setLIntegral_congr_fun hs.measurableSet
  intro u hu
  dsimp only
  rw [observationAt_eq_comp_split, observationPdf_comp_isometry]
  have hmark := spatial_mark_measurable Gamma u
    ((hG.contDiffAt (hs.mem_nhds hu)).differentiableAt_one) psi hpsi
  congr 1
  have he := regression_lintegral_comp_isometry (Gamma u) j 0
    (fun z => ENNReal.ofReal |(spatialJacobian Gamma z u).det| * psi z u) hmark
  rw [← he]
  apply lintegral_congr
  intro z
  rw [hH]

end
end SlowEquilibration.GaussianLocalCoordinates
