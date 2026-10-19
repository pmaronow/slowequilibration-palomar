-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.WeightedAreaFormula
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.FunProp
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Local coefficient incidence and weighted counting

The gradient is an actual smooth coefficient-linear function. An invertible
coefficient block gives its zero graph by algebra. The weighted equal-dimensional
area formula is applied to the joint incidence map, retaining the full coefficient
and spatial dependence of the Borel weight.
-/

@[expose] public section

namespace SlowEquilibration.CoefficientKacRice

open Set MeasureTheory MeasureTheory.Measure Function Filter
open scoped NNReal ENNReal Topology

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

/-- A local coordinate gradient, genuinely linear in the coefficients. -/
def gradient (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (z : E × F) (u : E) : E :=
  G1 u z.1 + G2 u z.2

/-- The coefficient-zero graph produced by the invertible first block. -/
def alpha (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (p : E × F) : E :=
  -((G1 p.1).inverse ((G2 p.1) p.2))

/-- The joint incidence map from position and remaining coefficients to all coefficients. -/
def incidence (a : E × F → E) (p : E × F) : E × F := (a p, p.2)

/-- The actual spatial partial derivative of the incidence graph. -/
def spatialDerivative (a : E × F → E) (p : E × F) : E →L[ℝ] E :=
  (fderiv ℝ a p).comp (ContinuousLinearMap.inl ℝ E F)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
lemma zero_iff_graph (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (u : E) (z : E × F) (hG : (G1 u).IsInvertible) :
    gradient G1 G2 z u = 0 ↔ z.1 = alpha G1 G2 (u, z.2) := by
  rcases hG with ⟨e, he⟩
  unfold gradient alpha
  simp only [← he, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.coe_coe]
  constructor
  · intro hz
    apply e.injective
    simpa using (add_eq_zero_iff_eq_neg.mp hz)
  · intro hz
    rw [hz, map_neg, e.apply_symm_apply]
    exact neg_add_cancel _

omit [FiniteDimensional ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
lemma alpha_contDiffOn (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (v : Set E) (hv : IsOpen v) (h1 : ContDiffOn ℝ 1 G1 v) (h2 : ContDiffOn ℝ 1 G2 v)
    (hinv : ∀ u ∈ v, (G1 u).IsInvertible) :
    ContDiffOn ℝ 1 (alpha G1 G2) (v ×ˢ (univ : Set F)) := by
  intro p hp
  have hG1 := (h1.contDiffAt (hv.mem_nhds hp.1)).comp p contDiffAt_fst
  have hG2 := (h2.contDiffAt (hv.mem_nhds hp.1)).comp p contDiffAt_fst
  have hGi := (hinv p.1 hp.1).contDiffAt_map_inverse.comp p hG1
  exact ((hGi.clm_apply (hG2.clm_apply contDiffAt_snd)).neg).contDiffWithinAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
lemma incidence_contDiffOn (a : E × F → E) (s : Set (E × F))
    (ha : ContDiffOn ℝ 1 a s) : ContDiffOn ℝ 1 (incidence a) s :=
  ha.prodMk contDiffOn_snd

/-- A block upper-triangular continuous linear map. -/
def upperBlock (A : E →L[ℝ] E) (B : F →L[ℝ] E) : (E × F) →L[ℝ] (E × F) :=
  (A.comp (ContinuousLinearMap.fst ℝ E F) + B.comp (ContinuousLinearMap.snd ℝ E F)).prod
    (ContinuousLinearMap.snd ℝ E F)

omit [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
lemma upperBlock_det (A : E →L[ℝ] E) (B : F →L[ℝ] E) : (upperBlock A B).det = A.det := by
  let e := Module.finBasis ℝ E
  let f := Module.finBasis ℝ F
  have hm : LinearMap.toMatrix (e.prod f) (e.prod f) (upperBlock A B : (E × F) →ₗ[ℝ] E × F) =
      Matrix.fromBlocks (LinearMap.toMatrix e e (A : E →ₗ[ℝ] E))
        (LinearMap.toMatrix f e (B : F →ₗ[ℝ] E)) 0
        (LinearMap.toMatrix f f (LinearMap.id : F →ₗ[ℝ] F)) := by
    ext (i | i) (j | j) <;> simp [upperBlock, LinearMap.toMatrix, Finsupp.single_apply, eq_comm]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (e.prod f), hm,
    Matrix.det_fromBlocks_zero₂₁, LinearMap.det_toMatrix, LinearMap.det_toMatrix,
    LinearMap.det_id, mul_one]

omit [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- The joint incidence Jacobian is exactly the determinant of the spatial derivative. -/
lemma incidence_det (a : E × F → E) (p : E × F) (ha : DifferentiableAt ℝ a p) :
    (fderiv ℝ (incidence a) p).det = (spatialDerivative a p).det := by
  have h := ha.hasFDerivAt.prodMk hasFDerivAt_snd
  have hlin : (fderiv ℝ a p).prod (ContinuousLinearMap.snd ℝ E F) =
      upperBlock (spatialDerivative a p)
        ((fderiv ℝ a p).comp (ContinuousLinearMap.inr ℝ E F)) := by
    apply ContinuousLinearMap.ext
    intro q
    apply Prod.ext
    · change (fderiv ℝ a p) q = (fderiv ℝ a p) (q.1, 0) + (fderiv ℝ a p) (0, q.2)
      rw [← map_add]
      congr 1
      simp
    · rfl

  rw [show fderiv ℝ (incidence a) p = (fderiv ℝ a p).prod
      (ContinuousLinearMap.snd ℝ E F) from h.fderiv, hlin]
  exact upperBlock_det _ _

/-- The actual count over coefficient-gradient zeros in one coordinate domain. -/
def graphCount (a : E × F → E) (v : Set E) (phi : (E × F) → E → ℝ≥0∞) (z : E × F) : ℝ≥0∞ :=
  ∑' u : {u : E | u ∈ v ∧ a (u, z.2) = z.1}, phi z u

def incidence_fiber_equiv (a : E × F → E) (v : Set E) (z : E × F) :
    {p : E × F | p ∈ v ×ˢ (univ : Set F) ∧ incidence a p = z} ≃
      {u : E | u ∈ v ∧ a (u, z.2) = z.1} where
  toFun p := ⟨p.1.1, p.2.1.1, by
    have h1 := congrArg Prod.fst p.2.2
    have h2 := congrArg Prod.snd p.2.2
    simpa [incidence, ← h2] using h1⟩
  invFun u := ⟨((u : E), z.2), ⟨u.2.1, mem_univ _⟩, Prod.ext u.2.2 rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg Prod.snd p.2.2).symm
  right_inv u := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Reindexing the incidence fiber keeps the full field-dependent Borel weight. -/
lemma incidence_fiber_weight (a : E × F → E) (v : Set E)
    (rho : E × F → ℝ≥0∞) (phi : (E × F) → E → ℝ≥0∞) (z : E × F) :
    WeightedAreaFormula.fiberSum (incidence a) (v ×ˢ (univ : Set F))
      (fun p => rho (incidence a p) * phi (incidence a p) p.1) z = rho z * graphCount a v phi z := by
  classical
  let e := incidence_fiber_equiv a v z
  unfold WeightedAreaFormula.fiberSum graphCount
  rw [← e.symm.tsum_eq]
  have he : ∀ u : {u : E | u ∈ v ∧ a (u, z.2) = z.1}, incidence a ((u : E), z.2) = z :=
    fun u => Prod.ext u.2.2 rfl
  change (∑' u : {u : E | u ∈ v ∧ a (u, z.2) = z.1},
    rho (incidence a ((u : E), z.2)) * phi (incidence a ((u : E), z.2)) u) = _
  simp_rw [he]
  exact ENNReal.tsum_mul_left

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ F] [CompleteSpace F] in
lemma graph_weight_measurable (a : E × F → E) (v : Set E)
    (ha : ContDiffOn ℝ 1 a (v ×ˢ (univ : Set F)))
    (rho : E × F → ℝ≥0∞) (hrho : Measurable rho)
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    Measurable (fun p : v ×ˢ (univ : Set F) => rho (incidence a p) * phi (incidence a p) p.1.1) := by
  have hg : Measurable (fun p : v ×ˢ (univ : Set F) => incidence a p) :=
    (incidence_contDiffOn a _ ha).continuousOn.domRestrict.measurable
  exact (hrho.comp hg).mul (hphi.comp (hg.prodMk measurable_subtype_coe.fst))

/-- Joint measurability is derived from the actual incidence area formula. -/
theorem graphCount_aemeasurable (μ : Measure (E × F)) [IsAddHaarMeasure μ]
    (a : E × F → E) (v : Set E) (hv : IsOpen v)
    (ha : ContDiffOn ℝ 1 a (v ×ˢ (univ : Set F)))
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    AEMeasurable (graphCount a v phi) μ := by
  have hw := graph_weight_measurable a v ha (fun _ => 1) measurable_const phi hphi
  have harea := WeightedAreaFormula.weighted_area_formula μ (incidence a)
    (v ×ˢ (univ : Set F)) (hv.prod isOpen_univ) (incidence_contDiffOn a _ ha)
    (fun p => (1 : ℝ≥0∞) * phi (incidence a p) p.1) hw
  have heq : WeightedAreaFormula.fiberSum (incidence a) (v ×ˢ (univ : Set F))
      (fun p => (1 : ℝ≥0∞) * phi (incidence a p) p.1) = graphCount a v phi := by
    funext z
    simpa only [one_mul] using incidence_fiber_weight a v (fun _ => 1) phi z
  rw [heq] at harea
  exact harea.1

/-- Local weighted coefficient incidence for an arbitrary genuine coefficient
density. No count, nondegeneracy, or area identity is an input assumption. -/
theorem density_incidence_formula (μ : Measure (E × F)) [IsAddHaarMeasure μ]
    (a : E × F → E) (v : Set E) (hv : IsOpen v)
    (ha : ContDiffOn ℝ 1 a (v ×ˢ (univ : Set F)))
    (rho : E × F → ℝ≥0∞) (hrho : Measurable rho)
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    (∫⁻ z, graphCount a v phi z ∂μ.withDensity rho) =
      ∫⁻ p in v ×ˢ (univ : Set F), ENNReal.ofReal |(spatialDerivative a p).det| *
        (rho (incidence a p) * phi (incidence a p) p.1) ∂μ := by
  have hm := graphCount_aemeasurable μ a v hv ha phi hphi
  have hw := graph_weight_measurable a v ha rho hrho phi hphi
  have harea := (WeightedAreaFormula.weighted_area_formula μ (incidence a)
    (v ×ˢ (univ : Set F)) (hv.prod isOpen_univ) (incidence_contDiffOn a _ ha)
    (fun p => rho (incidence a p) * phi (incidence a p) p.1) hw).2
  calc
    (∫⁻ z, graphCount a v phi z ∂μ.withDensity rho) =
        ∫⁻ z, rho z * graphCount a v phi z ∂μ :=
      lintegral_withDensity_eq_lintegral_mul₀ hrho.aemeasurable hm
    _ = ∫⁻ z, WeightedAreaFormula.fiberSum (incidence a) (v ×ˢ (univ : Set F))
        (fun p => rho (incidence a p) * phi (incidence a p) p.1) z ∂μ := by
      apply lintegral_congr
      intro z
      exact (incidence_fiber_weight a v rho phi z).symm
    _ = ∫⁻ p in v ×ˢ (univ : Set F), ENNReal.ofReal |(fderiv ℝ (incidence a) p).det| *
        (rho (incidence a p) * phi (incidence a p) p.1) ∂μ := harea
    _ = ∫⁻ p in v ×ˢ (univ : Set F), ENNReal.ofReal |(spatialDerivative a p).det| *
        (rho (incidence a p) * phi (incidence a p) p.1) ∂μ := by
      apply setLIntegral_congr_fun (hv.prod isOpen_univ).measurableSet
      intro p hp
      dsimp only
      rw [incidence_det a p ((ha.contDiffAt ((hv.prod isOpen_univ).mem_nhds hp)).differentiableAt_one)]

/-- Tonelli disintegrates the incidence formula over position and the genuine
remaining coefficient variables; joint measurability is proved from C1 regularity. -/
theorem density_incidence_formula_iterated
    (μ : Measure E) (ν : Measure F) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    (a : E × F → E) (s : Set E) (hs : IsOpen s)
    (ha : ContDiffOn ℝ 1 a (s ×ˢ (univ : Set F)))
    (rho : E × F → ℝ≥0∞) (hrho : Measurable rho)
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    (∫⁻ z, graphCount a s phi z ∂(μ.prod ν).withDensity rho) =
      ∫⁻ u in s, ∫⁻ v,
        ENNReal.ofReal |(spatialDerivative a (u, v)).det| *
          (rho (incidence a (u, v)) * phi (incidence a (u, v)) u) ∂ν ∂μ := by
  rw [density_incidence_formula (μ.prod ν) a s hs ha rho hrho phi hphi]
  have hj : Continuous (fun p : s ×ˢ (univ : Set F) => spatialDerivative a p) :=
    ((ha.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) le_rfl).domRestrict).clm_comp_const
      (ContinuousLinearMap.inl ℝ E F)
  have hm : Measurable (fun p : s ×ˢ (univ : Set F) =>
      ENNReal.ofReal |(spatialDerivative a p).det| *
        (rho (incidence a p) * phi (incidence a p) p.1.1)) :=
    (ENNReal.measurable_ofReal.comp
      (Continuous.abs (ContinuousLinearMap.continuous_det.comp hj)).measurable).mul
        (graph_weight_measurable a s ha rho hrho phi hphi)
  simpa only [Measure.restrict_univ] using
    (setLIntegral_prod (fun p : E × F => ENNReal.ofReal |(spatialDerivative a p).det| *
      (rho (incidence a p) * phi (incidence a p) p.1))
        (aemeasurable_restrict_of_measurable_subtype (hs.prod isOpen_univ).measurableSet hm))

/-- Critical points are counted by the actual gradient-zero predicate. -/
def gradientCount (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (v : Set E) (phi : (E × F) → E → ℝ≥0∞) (z : E × F) : ℝ≥0∞ :=
  ∑' u : {u : E | u ∈ v ∧ gradient G1 G2 z u = 0}, phi z u

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
lemma gradientCount_eq_graphCount (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (v : Set E) (hinv : ∀ u ∈ v, (G1 u).IsInvertible)
    (phi : (E × F) → E → ℝ≥0∞) (z : E × F) :
    gradientCount G1 G2 v phi z = graphCount (alpha G1 G2) v phi z := by
  unfold gradientCount graphCount
  have heq : {u : E | u ∈ v ∧ gradient G1 G2 z u = 0} =
      {u : E | u ∈ v ∧ alpha G1 G2 (u, z.2) = z.1} := by
    ext u
    constructor
    · intro hu
      exact ⟨hu.1, ((zero_iff_graph G1 G2 u z (hinv u hu.1)).mp hu.2).symm⟩
    · intro hu
      exact ⟨hu.1, (zero_iff_graph G1 G2 u z (hinv u hu.1)).mpr hu.2.symm⟩
  rw [heq]

/-- Borel coefficient- and location-dependent weights are admitted in the
actual gradient-counting formula; no continuity of the weight is required. -/
theorem local_gradient_density_formula (μ : Measure (E × F)) [IsAddHaarMeasure μ]
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (v : Set E) (hv : IsOpen v)
    (h1 : ContDiffOn ℝ 1 G1 v) (h2 : ContDiffOn ℝ 1 G2 v)
    (hinv : ∀ u ∈ v, (G1 u).IsInvertible)
    (rho : E × F → ℝ≥0∞) (hrho : Measurable rho)
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    (∫⁻ z, gradientCount G1 G2 v phi z ∂μ.withDensity rho) =
      ∫⁻ p in v ×ˢ (univ : Set F), ENNReal.ofReal |(spatialDerivative (alpha G1 G2) p).det| *
        (rho (incidence (alpha G1 G2) p) * phi (incidence (alpha G1 G2) p) p.1) ∂μ := by
  have heq : gradientCount G1 G2 v phi = graphCount (alpha G1 G2) v phi :=
    funext fun z => gradientCount_eq_graphCount G1 G2 v hinv phi z
  rw [heq]
  exact density_incidence_formula μ (alpha G1 G2) v hv (alpha_contDiffOn G1 G2 v hv h1 h2 hinv)
    rho hrho phi hphi


/-- The coordinate Hessian is the actual derivative of the coordinate gradient. -/
def coordinateHessian (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (z : E × F) (u : E) : E →L[ℝ] E := fderiv ℝ (gradient G1 G2 z) u

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
lemma spatial_hasFDerivAt (a : E × F → E) (u : E) (v : F)
    (ha : DifferentiableAt ℝ a (u, v)) :
    HasFDerivAt (fun t => a (t, v)) (spatialDerivative a (u, v)) u := by
  have hp : HasFDerivAt (fun t : E => (t, v)) (ContinuousLinearMap.inl ℝ E F) u := by
    have hd : (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] F) =
        ContinuousLinearMap.inl ℝ E F := by
      apply ContinuousLinearMap.ext
      intro q
      rfl
    rw [← hd]
    simpa only [id_eq] using (hasFDerivAt_id u).prodMk (hasFDerivAt_const v u)
  exact ha.hasFDerivAt.comp u hp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- The actual coordinate Hessian of a coefficient-linear gradient. -/
lemma coordinateHessian_eq (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (h1 : ContDiff ℝ 1 G1) (h2 : ContDiff ℝ 1 G2) (z : E × F) (u : E) :
    coordinateHessian G1 G2 z u =
      (fderiv ℝ G1 u).flip z.1 + (fderiv ℝ G2 u).flip z.2 := by
  have hfixed := ((h1.differentiable one_ne_zero u).hasFDerivAt.clm_apply
    (hasFDerivAt_const z.1 u)).add
    ((h2.differentiable one_ne_zero u).hasFDerivAt.clm_apply (hasFDerivAt_const z.2 u))
  have hfEq : gradient G1 G2 z = ((fun y => G1 y z.1) + fun y => G2 y z.2) := by
    funext y
    rfl
  unfold coordinateHessian
  rw [hfEq]
  simpa using hfixed.fderiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- Continuity of the actual joint coefficient/spatial Hessian follows from C1
regularity of the coefficient-gradient maps. -/
lemma coordinateHessian_continuous (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (h1 : ContDiff ℝ 1 G1) (h2 : ContDiff ℝ 1 G2) :
    Continuous (fun p : (E × F) × E => coordinateHessian G1 G2 p.1 p.2) := by
  simp_rw [coordinateHessian_eq G1 G2 h1 h2]
  exact (((ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp
    ((h1.continuous_fderiv one_ne_zero).comp continuous_snd)).clm_apply continuous_fst.fst).add
    (((ContinuousLinearMap.flipₗᵢ ℝ E F E).continuous.comp
      ((h2.continuous_fderiv one_ne_zero).comp continuous_snd)).clm_apply continuous_fst.snd)

omit [FiniteDimensional ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- Differentiating the genuine coefficient-zero equation yields the incidence
Jacobian/Hessian relation, before any determinant or area calculation. -/
theorem gradient_incidence_derivative (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (s : Set E) (hs : IsOpen s) (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) (u : E) (v : F) (hu : u ∈ s) :
    (G1 u).comp (spatialDerivative (alpha G1 G2) (u, v)) =
      -(coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u) := by
  let a := alpha G1 G2
  have ha := alpha_contDiffOn G1 G2 s hs h1 h2 hinv
  have had : DifferentiableAt ℝ a (u, v) :=
    (ha.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hu, mem_univ _⟩)).differentiableAt_one
  have hA := spatial_hasFDerivAt a u v had
  have hG1 := (h1.contDiffAt (hs.mem_nhds hu)).differentiableAt_one.hasFDerivAt
  have hG2 := (h2.contDiffAt (hs.mem_nhds hu)).differentiableAt_one.hasFDerivAt
  have htotal := (hG1.clm_apply hA).add (hG2.clm_apply (hasFDerivAt_const v u))
  have hfixed := (hG1.clm_apply (hasFDerivAt_const (a (u, v)) u)).add
    (hG2.clm_apply (hasFDerivAt_const v u))
  have hH : coordinateHessian G1 G2 (incidence a (u, v)) u =
      (fderiv ℝ G1 u).flip (a (u, v)) + (fderiv ℝ G2 u).flip v := by
    have hfEq : gradient G1 G2 (incidence a (u, v)) =
        ((fun y => G1 y (a (u, v))) + fun y => G2 y v) := by
      funext y
      rfl
    unfold coordinateHessian
    rw [hfEq]
    simpa using hfixed.fderiv
  have heq : (fun y => G1 y (a (y, v)) + G2 y v) =ᶠ[𝓝 u] (fun _ => (0 : E)) := by
    filter_upwards [hs.mem_nhds hu] with y hy
    exact (zero_iff_graph G1 G2 y (incidence a (y, v)) (hinv y hy)).mpr rfl
  have hzero : HasFDerivAt (fun y => G1 y (a (y, v)) + G2 y v) 0 u :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E) u).congr_of_eventuallyEq heq
  have hder := htotal.unique hzero
  have hder' : (G1 u).comp (spatialDerivative a (u, v)) +
      ((fderiv ℝ G1 u).flip (a (u, v)) + (fderiv ℝ G2 u).flip v) = 0 := by
    simpa only [ContinuousLinearMap.comp_zero, add_zero, zero_add, add_assoc] using hder
  rw [← hH] at hder'
  exact add_eq_zero_iff_eq_neg.mp hder'

omit [FiniteDimensional ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- Equation `kr-incidence-jacobian`, with the actual spatial derivatives. -/
theorem spatial_derivative_eq_inverse_hessian
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (s : Set E) (hs : IsOpen s) (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) (u : E) (v : F) (hu : u ∈ s) :
    spatialDerivative (alpha G1 G2) (u, v) =
      -((G1 u).inverse.comp (coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u)) := by
  have h := gradient_incidence_derivative G1 G2 s hs h1 h2 hinv u v hu
  calc
    spatialDerivative (alpha G1 G2) (u, v) =
        (G1 u).inverse.comp ((G1 u).comp (spatialDerivative (alpha G1 G2) (u, v))) := by
      rw [← ContinuousLinearMap.comp_assoc, (hinv u hu).inverse_comp_self,
        ContinuousLinearMap.id_comp]
    _ = -((G1 u).inverse.comp (coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u)) := by
      rw [h, ContinuousLinearMap.comp_neg]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
lemma invertible_det_ne_zero (A : E →L[ℝ] E) (hA : A.IsInvertible) : A.det ≠ 0 := by
  rcases hA with ⟨e, rfl⟩
  exact e.toLinearEquiv.isUnit_det'.ne_zero

omit [FiniteDimensional ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- The exact Jacobian factor in the local coefficient Kac--Rice formula. -/
theorem spatial_abs_det_hessian (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (s : Set E) (hs : IsOpen s) (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) (u : E) (v : F) (hu : u ∈ s) :
    |(spatialDerivative (alpha G1 G2) (u, v)).det| =
      |(coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u).det| / |(G1 u).det| := by
  have hrel := gradient_incidence_derivative G1 G2 s hs h1 h2 hinv u v hu
  have hd := congrArg ContinuousLinearMap.det hrel
  have hneg : (-(coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u)).det =
      (-1 : ℝ) ^ Module.finrank ℝ E *
        (coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u).det := by
    change LinearMap.det (-(coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u : E →ₗ[ℝ] E)) = _
    rw [← neg_one_smul ℝ, LinearMap.det_smul]
  rw [hneg] at hd
  change LinearMap.det ((G1 u : E →ₗ[ℝ] E).comp
    (spatialDerivative (alpha G1 G2) (u, v) : E →ₗ[ℝ] E)) = _ at hd
  rw [LinearMap.det_comp] at hd
  have habs := congrArg abs hd
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  apply (eq_div_iff (abs_ne_zero.mpr (invertible_det_ne_zero _ (hinv u hu)))).2
  simpa only [mul_comm] using habs

omit [FiniteDimensional ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- Degeneracy of the incidence map is exactly degeneracy of the actual Hessian. -/
theorem spatial_det_zero_iff_hessian (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (s : Set E) (hs : IsOpen s) (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) (u : E) (v : F) (hu : u ∈ s) :
    (spatialDerivative (alpha G1 G2) (u, v)).det = 0 ↔
      (coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u).det = 0 := by
  rw [← abs_eq_zero, spatial_abs_det_hessian G1 G2 s hs h1 h2 hinv u v hu]
  simp only [div_eq_zero_iff, abs_eq_zero, invertible_det_ne_zero _ (hinv u hu), or_false]

/-- The local set of coefficients with an actual degenerate gradient zero. -/
def localDegenerateCoefficients (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (s : Set E) : Set (E × F) :=
  {z | ∃ u ∈ s, gradient G1 G2 z u = 0 ∧ (coordinateHessian G1 G2 z u).det = 0}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- On an actual compact spatial set, the degenerate-coefficient set is
closed by projection of the genuine closed zero-Hessian incidence relation. -/
theorem compact_degenerate_coefficients_closed
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (h1 : ContDiff ℝ 1 G1) (h2 : ContDiff ℝ 1 G2) (K : Set E) (hK : IsCompact K) :
    IsClosed (localDegenerateCoefficients G1 G2 K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let rel : Set ((E × F) × K) :=
    {p | gradient G1 G2 p.1 p.2 = 0 ∧ (coordinateHessian G1 G2 p.1 p.2).det = 0}
  have hg : Continuous (fun p : (E × F) × K => gradient G1 G2 p.1 p.2) :=
    ((h1.continuous.comp (continuous_subtype_val.comp continuous_snd)).clm_apply continuous_fst.fst).add
      ((h2.continuous.comp (continuous_subtype_val.comp continuous_snd)).clm_apply continuous_fst.snd)
  have hh : Continuous (fun p : (E × F) × K => (coordinateHessian G1 G2 p.1 p.2).det) :=
    ContinuousLinearMap.continuous_det.comp
      ((coordinateHessian_continuous G1 G2 h1 h2).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hr : IsClosed rel := (isClosed_eq hg continuous_const).inter (isClosed_eq hh continuous_const)
  have heq : localDegenerateCoefficients G1 G2 K = Prod.fst '' rel := by
    ext z
    constructor
    · rintro ⟨u, hu, hg, hh⟩
      exact ⟨(z, ⟨u, hu⟩), ⟨hg, hh⟩, rfl⟩
    · rintro ⟨⟨z, u⟩, ⟨hg, hh⟩, rfl⟩
      exact ⟨u, u.2, hg, hh⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace rel hr

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- Actual nondegenerate gradient zeros in a compact spatial set are finite:
the inverse function theorem isolates each zero and compactness finishes. -/
theorem compact_regular_gradient_zeros_finite
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (h1 : ContDiff ℝ 1 G1) (h2 : ContDiff ℝ 1 G2) (K : Set E) (hK : IsCompact K)
    (z : E × F) (hz : z ∉ localDegenerateCoefficients G1 G2 K) :
    {u : E | u ∈ K ∧ gradient G1 G2 z u = 0}.Finite := by
  let f := gradient G1 G2 z
  have hf : ContDiff ℝ 1 f := (h1.clm_apply contDiff_const).add (h2.clm_apply contDiff_const)
  have hc : IsCompact {u : E | u ∈ K ∧ f u = 0} :=
    hK.inter_right (isClosed_eq hf.continuous continuous_const)
  apply hc.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro u hu
  have hreg : u ∈ WeightedAreaFormula.regularSet f univ := by
    refine ⟨mem_univ _, ?_⟩
    intro hdet
    exact hz ⟨u, hu.1, hu.2, hdet⟩
  obtain ⟨v, hv, huv, _, hinj⟩ := WeightedAreaFormula.regular_inverse_neighborhood f univ
    isOpen_univ hf.contDiffOn u hreg
  refine ⟨v, hv, ?_⟩
  ext w
  constructor
  · intro hw
    exact (hinj hw.1 huv (hw.2.2.trans hu.2.symm))
  · rintro rfl
    exact ⟨huv, hu⟩

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- The actual degenerate-coefficient set equals the critical-value set of
its genuine joint incidence map. -/
theorem localDegenerateCoefficients_eq_critical_values
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (s : Set E) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) :
    localDegenerateCoefficients G1 G2 s = incidence (alpha G1 G2) ''
      WeightedAreaFormula.criticalSet (incidence (alpha G1 G2)) (s ×ˢ (univ : Set F)) := by
  let a := alpha G1 G2
  have ha := alpha_contDiffOn G1 G2 s hs h1 h2 hinv
  ext z
  constructor
  · rintro ⟨u, hu, hz, hh⟩
    have hg : incidence a (u, z.2) = z :=
      Prod.ext (((zero_iff_graph G1 G2 u z (hinv u hu)).mp hz).symm) rfl
    refine ⟨(u, z.2), ⟨⟨hu, mem_univ _⟩, ?_⟩, hg⟩
    rw [incidence_det a (u, z.2)
      ((ha.contDiffAt ((hs.prod isOpen_univ).mem_nhds ⟨hu, mem_univ _⟩)).differentiableAt_one)]
    apply (spatial_det_zero_iff_hessian G1 G2 s hs h1 h2 hinv u z.2 hu).mpr
    change (coordinateHessian G1 G2 (incidence a (u, z.2)) u).det = 0
    rw [hg]
    exact hh
  · rintro ⟨p, hp, hz⟩
    have hu : p.1 ∈ s := hp.1.1
    have hd : (spatialDerivative a p).det = 0 := by
      rw [← incidence_det a p
        ((ha.contDiffAt ((hs.prod isOpen_univ).mem_nhds hp.1)).differentiableAt_one)]
      exact hp.2
    have hh := (spatial_det_zero_iff_hessian G1 G2 s hs h1 h2 hinv p.1 p.2 hu).mp hd
    refine ⟨p.1, hu, ?_, ?_⟩
    · rw [← hz]
      exact (zero_iff_graph G1 G2 p.1 (incidence a p) (hinv p.1 hu)).mpr rfl
    · change (coordinateHessian G1 G2 (incidence a p) p.1).det = 0 at hh
      rw [hz] at hh
      exact hh


omit [SecondCountableTopology E] [CompleteSpace F] in
/-- Degenerate coefficients in a coordinate chart are Lebesgue/Haar null,
proved by applying equal-dimensional Sard to the genuine joint incidence map. -/
theorem local_degenerate_coefficients_null (μ : Measure (E × F)) [IsAddHaarMeasure μ]
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (s : Set E) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) :
    μ (localDegenerateCoefficients G1 G2 s) = 0 := by
  let a := alpha G1 G2
  have ha := alpha_contDiffOn G1 G2 s hs h1 h2 hinv
  rw [localDegenerateCoefficients_eq_critical_values G1 G2 s hs h1 h2 hinv]
  exact WeightedAreaFormula.critical_values_null μ (incidence a) _ (hs.prod isOpen_univ)
    (incidence_contDiffOn a _ ha)

/-- The actual coefficient-zero count is Borel on the regular-coefficient
subspace, including arbitrary full coefficient-dependent nonnegative weights. -/
theorem regular_gradientCount_measurable
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (s : Set E) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible)
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    Measurable (fun z : {z : E × F | z ∉ localDegenerateCoefficients G1 G2 s} =>
      gradientCount G1 G2 s phi z) := by
  let a := alpha G1 G2
  have ha := alpha_contDiffOn G1 G2 s hs h1 h2 hinv
  have heq := localDegenerateCoefficients_eq_critical_values G1 G2 s hs h1 h2 hinv
  have hmeas := WeightedAreaFormula.regular_values_fiberSum_measurable
    (incidence a) (s ×ˢ (univ : Set F)) (hs.prod isOpen_univ)
    (incidence_contDiffOn a _ ha) (fun p => phi (incidence a p) p.1)
    (by simpa only [one_mul] using
      graph_weight_measurable a s ha (fun _ => 1) measurable_const phi hphi)
  have hsub : Measurable (fun z : {z : E × F | z ∉ localDegenerateCoefficients G1 G2 s} =>
      (⟨(z : E × F), by rw [← heq]; exact z.2⟩ :
        {z : E × F | z ∉ incidence a '' WeightedAreaFormula.criticalSet (incidence a)
          (s ×ˢ (univ : Set F))})) := measurable_subtype_coe.subtype_mk
  have hm := hmeas.comp hsub
  convert hm using 1
  funext z
  rw [gradientCount_eq_graphCount G1 G2 s hinv phi]
  change graphCount a s phi z = WeightedAreaFormula.fiberSum (incidence a)
    (s ×ˢ (univ : Set F)) (fun p => phi (incidence a p) p.1) z
  simpa only [one_mul] using
    (incidence_fiber_weight a s (fun _ => 1) phi z).symm

omit [SecondCountableTopology E] [CompleteSpace F] in
/-- The same null statement holds for every genuinely absolutely continuous
coefficient law, in particular every nondegenerate finite Gaussian law. -/
theorem local_degenerate_coefficients_null_of_ac (μ ν : Measure (E × F)) [IsAddHaarMeasure μ]
    (hac : ν ≪ μ) (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (s : Set E) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) :
    ν (localDegenerateCoefficients G1 G2 s) = 0 :=
  hac (local_degenerate_coefficients_null μ G1 G2 s hs h1 h2 hinv)

/-- The local coefficient-incidence formula with the actual Hessian determinant
and the exact inverse coefficient-block Jacobian. -/
theorem local_hessian_density_formula (μ : Measure (E × F)) [IsAddHaarMeasure μ]
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E) (s : Set E) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible)
    (rho : E × F → ℝ≥0∞) (hrho : Measurable rho)
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    (∫⁻ z, gradientCount G1 G2 s phi z ∂μ.withDensity rho) =
      ∫⁻ p in s ×ˢ (univ : Set F),
        ENNReal.ofReal (|(coordinateHessian G1 G2 (incidence (alpha G1 G2) p) p.1).det| / |(G1 p.1).det|) *
          (rho (incidence (alpha G1 G2) p) * phi (incidence (alpha G1 G2) p) p.1) ∂μ := by
  rw [local_gradient_density_formula μ G1 G2 s hs h1 h2 hinv rho hrho phi hphi]
  apply setLIntegral_congr_fun (hs.prod isOpen_univ).measurableSet
  intro p hp
  dsimp only
  rw [spatial_abs_det_hessian G1 G2 s hs h1 h2 hinv p.1 p.2 hp.1]


/-- The actual local Hessian formula as a position integral of coefficient
fiber integrals, with no conditional expectation or density assumed. -/
theorem local_hessian_density_formula_iterated
    (μ : Measure E) (ν : Measure F) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    (G1 : E → E →L[ℝ] E) (G2 : E → F →L[ℝ] E)
    (s : Set E) (hs : IsOpen s) (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible)
    (rho : E × F → ℝ≥0∞) (hrho : Measurable rho)
    (phi : (E × F) → E → ℝ≥0∞) (hphi : Measurable fun p : (E × F) × E => phi p.1 p.2) :
    (∫⁻ z, gradientCount G1 G2 s phi z ∂(μ.prod ν).withDensity rho) =
      ∫⁻ u in s, ∫⁻ v,
        ENNReal.ofReal (|(coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u).det| / |(G1 u).det|) *
          (rho (incidence (alpha G1 G2) (u, v)) * phi (incidence (alpha G1 G2) (u, v)) u) ∂ν ∂μ := by
  have heq : gradientCount G1 G2 s phi = graphCount (alpha G1 G2) s phi :=
    funext fun z => gradientCount_eq_graphCount G1 G2 s hinv phi z
  rw [heq, density_incidence_formula_iterated μ ν (alpha G1 G2) s hs
    (alpha_contDiffOn G1 G2 s hs h1 h2 hinv) rho hrho phi hphi]
  apply setLIntegral_congr_fun hs.measurableSet
  intro u hu
  apply lintegral_congr
  intro v
  rw [spatial_abs_det_hessian G1 G2 s hs h1 h2 hinv u v hu]

/-- A finite vector of genuine independent standard real Gaussians is
absolutely continuous with respect to the actual product Lebesgue measure. -/
theorem gaussian_pi_absolutelyContinuous (n : ℕ) :
    (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) ≪
      (volume : Measure (Fin n → ℝ)) := by
  induction n with
  | zero =>
      change (Measure.pi (fun _ : Fin 0 => ProbabilityTheory.gaussianReal 0 1)) ≪
        Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ))
      have heq : (fun _ : Fin 0 => ProbabilityTheory.gaussianReal 0 1) =
          (fun _ : Fin 0 => (volume : Measure ℝ)) := by
        funext i
        exact Fin.elim0 i
      rw [heq]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hG := (MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 1) 0).symm
      have hV := (MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0).symm
      have hac := (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).prod ih
      have hmap := e.symm.measurableEmbedding.absolutelyContinuous_map hac
      have hV' : ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).map e.symm =
          (volume : Measure (Fin (n + 1) → ℝ)) := hV.map_eq
      rw [hV'] at hmap
      simpa only [e, hG.map_eq] using hmap

/-- Genuine Euclidean standard Gaussians have a Lebesgue density in every finite dimension. -/
theorem stdGaussian_absolutelyContinuous (n : ℕ) :
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) ≪
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hmap := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding.absolutelyContinuous_map
    (gaussian_pi_absolutelyContinuous n)
  change (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)).map (WithLp.toLp 2) ≪
    (volume : Measure (Fin n → ℝ)).map (WithLp.toLp 2) at hmap
  rw [ProbabilityTheory.map_pi_eq_stdGaussian, (PiLp.volume_preserving_toLp (Fin n)).map_eq] at hmap
  exact hmap

/-- The actual independent standard Gaussian coefficient law in a coefficient-block split. -/
def gaussianCoefficientLaw (n m : ℕ) : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))

/-- The actual matching coefficient-space Lebesgue measure. -/
def coefficientVolume (n m : ℕ) : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).prod
    (volume : Measure (EuclideanSpace ℝ (Fin m)))

instance coefficientVolume_isAddHaarMeasure (n m : ℕ) : IsAddHaarMeasure (coefficientVolume n m) :=
  inferInstanceAs (IsAddHaarMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
    (volume : Measure (EuclideanSpace ℝ (Fin m)))))

instance coefficientVolume_sigmaFinite (n m : ℕ) : SigmaFinite (coefficientVolume n m) :=
  inferInstanceAs (SigmaFinite ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
    (volume : Measure (EuclideanSpace ℝ (Fin m)))))

instance gaussianCoefficientLaw_isProbabilityMeasure (n m : ℕ) : IsProbabilityMeasure (gaussianCoefficientLaw n m) :=
  inferInstanceAs (IsProbabilityMeasure ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))))

lemma gaussianCoefficientLaw_ac (n m : ℕ) : gaussianCoefficientLaw n m ≪ coefficientVolume n m :=
  (stdGaussian_absolutelyContinuous n).prod (stdGaussian_absolutelyContinuous m)

/-- A canonical genuine density of the Gaussian coefficient law. This is its
Radon--Nikodym derivative, not a newly postulated Gaussian law. -/
def gaussianCoefficientDensity (n m : ℕ) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ≥0∞ :=
  (gaussianCoefficientLaw n m).rnDeriv (coefficientVolume n m)

lemma gaussianCoefficientDensity_measurable (n m : ℕ) : Measurable (gaussianCoefficientDensity n m) :=
  Measure.measurable_rnDeriv _ _

lemma gaussianCoefficientLaw_density (n m : ℕ) :
    (coefficientVolume n m).withDensity (gaussianCoefficientDensity n m) = gaussianCoefficientLaw n m :=
  Measure.withDensity_rnDeriv_eq _ _ (gaussianCoefficientLaw_ac n m)

/-- The actual Gaussian coefficient law almost surely has no degenerate zero
in a coefficient chart; no Gaussian density or nullity is assumed. -/
theorem gaussian_local_degenerate_coefficients_null (n m : ℕ)
    (G1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible) :
    gaussianCoefficientLaw n m (localDegenerateCoefficients G1 G2 s) = 0 :=
  local_degenerate_coefficients_null_of_ac (coefficientVolume n m) (gaussianCoefficientLaw n m)
    (gaussianCoefficientLaw_ac n m) G1 G2 s hs h1 h2 hinv

/-- Actual Gaussian coefficients almost surely have only finitely many
coordinate-gradient zeros in every specified compact chart region. -/
theorem gaussian_compact_gradient_zeros_finite_ae (n m : ℕ)
    (G1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (h1 : ContDiff ℝ 1 G1) (h2 : ContDiff ℝ 1 G2)
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsOpen s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∀ᵐ z ∂gaussianCoefficientLaw n m,
      {u | u ∈ K ∧ gradient G1 G2 z u = 0}.Finite := by
  have hn := gaussian_local_degenerate_coefficients_null n m G1 G2 s hs h1.contDiffOn h2.contDiffOn hinv
  have hsub : {z | ¬ {u | u ∈ K ∧ gradient G1 G2 z u = 0}.Finite} ⊆
      localDegenerateCoefficients G1 G2 s := by
    intro z hz
    by_contra hbad
    apply hz
    apply compact_regular_gradient_zeros_finite G1 G2 h1 h2 K hK z
    rintro ⟨u, hu, hg, hh⟩
    exact hbad ⟨u, hKs hu, hg, hh⟩
  exact ae_iff.mpr (measure_mono_null hsub hn)

/-- The genuine Gaussian local coefficient-incidence formula. The Gaussian
law and its density are derived above; full coefficient dependence is retained. -/
theorem gaussian_local_hessian_formula (n m : ℕ)
    (G1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible)
    (phi : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hphi : Measurable fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin n) => phi p.1 p.2) :
    (∫⁻ z, gradientCount G1 G2 s phi z ∂gaussianCoefficientLaw n m) =
      ∫⁻ p in s ×ˢ (univ : Set (EuclideanSpace ℝ (Fin m))),
        ENNReal.ofReal (|(coordinateHessian G1 G2 (incidence (alpha G1 G2) p) p.1).det| / |(G1 p.1).det|) *
          (gaussianCoefficientDensity n m (incidence (alpha G1 G2) p) *
            phi (incidence (alpha G1 G2) p) p.1) ∂coefficientVolume n m := by
  rw [← gaussianCoefficientLaw_density n m]
  exact local_hessian_density_formula (coefficientVolume n m) G1 G2 s hs h1 h2 hinv
    (gaussianCoefficientDensity n m) (gaussianCoefficientDensity_measurable n m) phi hphi

/-- The actual Gaussian counting expectation in the iterated coefficient-incidence
form used immediately before conditional-Gaussian identification. -/
theorem gaussian_local_hessian_formula_iterated (n m : ℕ)
    (G1 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 1 G1 s) (h2 : ContDiffOn ℝ 1 G2 s)
    (hinv : ∀ u ∈ s, (G1 u).IsInvertible)
    (phi : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hphi : Measurable fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin n) => phi p.1 p.2) :
    (∫⁻ z, gradientCount G1 G2 s phi z ∂gaussianCoefficientLaw n m) =
      ∫⁻ u in s, ∫⁻ v,
        ENNReal.ofReal (|(coordinateHessian G1 G2 (incidence (alpha G1 G2) (u, v)) u).det| / |(G1 u).det|) *
          (gaussianCoefficientDensity n m (incidence (alpha G1 G2) (u, v)) *
            phi (incidence (alpha G1 G2) (u, v)) u) ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  rw [← gaussianCoefficientLaw_density n m]
  exact local_hessian_density_formula_iterated volume volume G1 G2 s hs h1 h2 hinv
    (gaussianCoefficientDensity n m) (gaussianCoefficientDensity_measurable n m) phi hphi


end
end SlowEquilibration.CoefficientKacRice
