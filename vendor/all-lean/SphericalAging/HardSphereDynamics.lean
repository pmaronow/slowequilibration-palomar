module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import SphericalAging.FiniteModel
public import FourPapersCommon.FilteredContinuousBrownianIntegral
public import FourPapersCommon.FilteredItoContinuous

public section

/-!
# Finite-dimensional coefficients of the hard-sphere diffusion

The state space and normalization agree with Chapter 3: vectors in `ℝ^N`,
the sphere `⟪x,x⟫ = N`, projection `I - xxᵀ/N`, noise `√2 P_x`,
and curvature drift `-(N-1)x/N`.

These declarations prove coefficient identities. They do not count
existence, uniqueness, sphere invariance, or stochastic flow construction as
assumptions or as established theorems.
-/

noncomputable section

namespace SphericalAging.HardSphereDynamics

open scoped BigOperators InnerProductSpace RealInnerProductSpace

@[expose] abbrev State (N : ℕ) := EuclideanSpace ℝ (Fin N)

@[expose] def radiusDefect {N : ℕ} (x : State N) : ℝ := ⟪x, x⟫_ℝ - N

@[expose] def OnSphere {N : ℕ} (x : State N) : Prop := ⟪x, x⟫_ℝ = N

@[expose] def kappa (N : ℕ) : ℝ := ((N : ℝ) - 1) / N

@[expose] def projection {N : ℕ} (x v : State N) : State N :=
  v - (⟪x, v⟫_ℝ / N) • x

@[expose] def basisVector {N : ℕ} (i : Fin N) : State N := EuclideanSpace.single i 1

@[expose] def noiseColumn {N : ℕ} (x : State N) (i : Fin N) : State N :=
  Real.sqrt 2 • projection x (basisVector i)

@[expose] def drift {N : ℕ} (β : ℝ) (gradient : State N → State N) (x : State N) : State N :=
  β • projection x (gradient x) - kappa N • x

@[expose] def hamiltonianGradient {N p : ℕ} (J : FiniteModel.Disorder N p) : State N → State N :=
  gradient (FiniteModel.Hamiltonian N p J)

@[expose] def hamiltonianDrift {N p : ℕ} (β : ℝ) (J : FiniteModel.Disorder N p) : State N → State N :=
  drift β (hamiltonianGradient J)

theorem radiusDefect_eq_norm_sq_sub {N : ℕ} (x : State N) :
    radiusDefect x = ‖x‖ ^ 2 - N := by
  simp only [radiusDefect, real_inner_self_eq_norm_sq]

theorem onSphere_iff_norm_sq {N : ℕ} (x : State N) :
    OnSphere x ↔ ‖x‖ ^ 2 = N := by
  simp only [OnSphere, real_inner_self_eq_norm_sq]

theorem projection_radial {N : ℕ} (hN : N ≠ 0) (x v : State N) :
    ⟪x, projection x v⟫_ℝ = -(radiusDefect x / N) * ⟪x, v⟫_ℝ := by
  unfold projection radiusDefect
  rw [inner_sub_right, real_inner_smul_right]
  field_simp
  ring

theorem projection_tangent {N : ℕ} (hN : N ≠ 0) (x v : State N)
    (hx : OnSphere x) : ⟪x, projection x v⟫_ℝ = 0 := by
  rw [projection_radial hN]
  have hz : radiusDefect x = 0 := by
    unfold radiusDefect
    rw [hx]
    simp
  rw [hz]
  simp

theorem projection_normal_zero {N : ℕ} (hN : N ≠ 0) (x : State N)
    (hx : OnSphere x) : projection x x = 0 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold projection
  rw [hx, div_self hn, one_smul, sub_self]

theorem projection_tangent_fixed {N : ℕ} (x v : State N)
    (hv : ⟪x, v⟫_ℝ = 0) : projection x v = v := by
  simp [projection, hv]

theorem projection_idempotent {N : ℕ} (hN : N ≠ 0) (x v : State N)
    (hx : OnSphere x) : projection x (projection x v) = projection x v := by
  exact projection_tangent_fixed x _ (projection_tangent hN x v hx)

theorem projection_self_adjoint {N : ℕ} (x u v : State N) :
    ⟪projection x u, v⟫_ℝ = ⟪u, projection x v⟫_ℝ := by
  simp only [projection, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm u x]
  ring

theorem projection_add {N : ℕ} (x u v : State N) :
    projection x (u + v) = projection x u + projection x v := by
  simp only [projection, inner_add_right, add_div, add_smul]
  module

theorem projection_smul {N : ℕ} (x v : State N) (a : ℝ) :
    projection x (a • v) = a • projection x v := by
  simp only [projection, real_inner_smul_right, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

theorem basis_inner {N : ℕ} (x : State N) (i : Fin N) :
    ⟪x, basisVector i⟫_ℝ = x i := by
  simp [basisVector, EuclideanSpace.inner_single_right]

theorem noise_radial {N : ℕ} (hN : N ≠ 0) (x : State N) (i : Fin N) :
    ⟪x, noiseColumn x i⟫_ℝ =
      -(radiusDefect x / N) * (Real.sqrt 2 * x i) := by
  unfold noiseColumn
  rw [real_inner_smul_right, projection_radial hN, basis_inner]
  ring

theorem noise_tangent {N : ℕ} (hN : N ≠ 0) (x : State N)
    (hx : OnSphere x) (i : Fin N) : ⟪x, noiseColumn x i⟫_ℝ = 0 := by
  unfold noiseColumn
  rw [real_inner_smul_right, projection_tangent hN x _ hx, mul_zero]

theorem drift_radial {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    (gradient : State N → State N) (x : State N) :
    ⟪x, drift β gradient x⟫_ℝ =
      -β * (radiusDefect x / N) * ⟪x, gradient x⟫_ℝ - kappa N * ⟪x,x⟫_ℝ := by
  unfold drift
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, projection_radial hN]
  ring

theorem drift_radial_onSphere {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    (gradient : State N → State N) (x : State N) (hx : OnSphere x) :
    ⟪x, drift β gradient x⟫_ℝ = -((N : ℝ) - 1) := by
  unfold drift
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    projection_tangent hN x _ hx, hx]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp [kappa, hn]

theorem projection_inner_self {N : ℕ} (x v : State N) :
    ⟪projection x v, projection x v⟫_ℝ =
      ⟪v,v⟫_ℝ - 2 * (⟪x,v⟫_ℝ / N) * ⟪x,v⟫_ℝ +
        (⟪x,v⟫_ℝ / N) ^ 2 * ⟪x,x⟫_ℝ := by
  simp only [projection, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v x]
  ring

theorem coordinate_square_sum {N : ℕ} (x : State N) :
    ∑ i : Fin N, (x i) ^ 2 = ⟪x,x⟫_ℝ := by
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]

theorem projection_basis_inner_self {N : ℕ} (x : State N) (i : Fin N) :
    ⟪projection x (basisVector i), projection x (basisVector i)⟫_ℝ =
      1 - (2 / (N : ℝ)) * (x i) ^ 2 +
        (⟪x,x⟫_ℝ / (N : ℝ) ^ 2) * (x i) ^ 2 := by
  rw [projection_inner_self]
  have hunit : ⟪basisVector i, basisVector i⟫_ℝ = 1 := by
    simp [basisVector]
  rw [hunit]
  simp only [basis_inner]
  ring

@[expose] def projectionTraceSquare {N : ℕ} (x : State N) : ℝ :=
  ∑ i : Fin N, ⟪projection x (basisVector i), projection x (basisVector i)⟫_ℝ

theorem projectionTraceSquare_formula {N : ℕ} (x : State N) :
    projectionTraceSquare x = N - 2 * ⟪x,x⟫_ℝ / N +
      ⟪x,x⟫_ℝ ^ 2 / (N : ℝ) ^ 2 := by
  unfold projectionTraceSquare
  simp_rw [projection_basis_inner_self]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ←Finset.mul_sum, ←Finset.mul_sum, coordinate_square_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

theorem projectionTraceSquare_onSphere {N : ℕ} (hN : N ≠ 0)
    (x : State N) (hx : OnSphere x) : projectionTraceSquare x = (N : ℝ) - 1 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [projectionTraceSquare_formula, hx]
  field_simp
  ring

@[expose] def noiseQuadraticTrace {N : ℕ} (x : State N) : ℝ :=
  ∑ i : Fin N, ⟪noiseColumn x i, noiseColumn x i⟫_ℝ

theorem noiseQuadraticTrace_eq {N : ℕ} (x : State N) :
    noiseQuadraticTrace x = 2 * projectionTraceSquare x := by
  unfold noiseQuadraticTrace noiseColumn projectionTraceSquare
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [←mul_assoc, ←pow_two, hs]

@[expose] def radialGenerator {N : ℕ} (β : ℝ) (gradient : State N → State N) (x : State N) : ℝ :=
  2 * ⟪x, drift β gradient x⟫_ℝ + noiseQuadraticTrace x

/-- Exact drift factorization for the radial Itô equation before any use of
sphere invariance. The gradient is arbitrary in this algebraic identity. -/
theorem radialGenerator_factor {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    (gradient : State N → State N) (x : State N) :
    radialGenerator β gradient x = radiusDefect x *
      (-2 * β * ⟪x,gradient x⟫_ℝ / N + 2 * ⟪x,x⟫_ℝ / (N : ℝ) ^ 2 - 2) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  unfold radialGenerator
  rw [drift_radial hN, noiseQuadraticTrace_eq, projectionTraceSquare_formula]
  unfold radiusDefect kappa
  field_simp
  ring

theorem radialNoise_factor {N : ℕ} (hN : N ≠ 0) (x : State N) (i : Fin N) :
    2 * ⟪x, noiseColumn x i⟫_ℝ =
      radiusDefect x * (-2 * Real.sqrt 2 * x i / N) := by
  rw [noise_radial hN]
  ring

theorem radialGenerator_onSphere {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    (gradient : State N → State N) (x : State N) (hx : OnSphere x) :
    radialGenerator β gradient x = 0 := by
  rw [radialGenerator_factor hN]
  have hz : radiusDefect x = 0 := by
    unfold radiusDefect
    rw [hx]
    simp
  rw [hz, zero_mul]

theorem noiseCoordinate_formula {N : ℕ} (x : State N) (i j : Fin N) :
    (noiseColumn x j) i =
      Real.sqrt 2 * ((if i = j then 1 else 0) - x i * x j / N) := by
  simp only [noiseColumn, projection, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
    basisVector, PiLp.single_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  ring

theorem continuous_noiseCoordinate {N : ℕ} (i j : Fin N) :
    Continuous (fun x : State N => (noiseColumn x j) i) := by
  simp_rw [noiseCoordinate_formula]
  exact continuous_const.mul (continuous_const.sub
    (((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).mul
      (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) j)).div_const _))

/-! The differential of the projection is calculated in the ambient space.
These formulas provide the actual coefficients of the variational SDE. -/

@[expose] def projectionDerivative {N : ℕ} (x h v : State N) : State N :=
  -(⟪h, v⟫_ℝ / N) • x - (⟪x, v⟫_ℝ / N) • h

theorem projection_increment {N : ℕ} (x h v : State N) :
    projection (x + h) v - projection x v =
      projectionDerivative x h v - (⟪h, v⟫_ℝ / N) • h := by
  simp only [projection, projectionDerivative, inner_add_left, add_div, add_smul,
    smul_add, neg_smul]
  module

theorem differentiable_projection {N : ℕ} (v : State N) :
    Differentiable ℝ (fun x : State N => projection x v) := by
  intro x
  have hi : DifferentiableAt ℝ (fun y : State N => ⟪y, v⟫_ℝ) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  simpa only [projection, div_eq_mul_inv, id_eq] using
    (differentiableAt_const v).fun_sub
      ((hi.mul_const (N : ℝ)⁻¹).fun_smul (f := fun y : State N => y) differentiableAt_id)

theorem fderiv_projection_apply {N : ℕ} (x h v : State N) :
    fderiv ℝ (fun y : State N => projection y v) x h =
      projectionDerivative x h v := by
  simp only [projection]
  have hi : DifferentiableAt ℝ (fun y : State N => ⟪y, v⟫_ℝ) x :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  simp only [div_eq_mul_inv]
  rw [fderiv_const_sub,
    fderiv_fun_smul (c := fun y : State N => ⟪y, v⟫_ℝ * (N : ℝ)⁻¹)
      (f := fun y : State N => y) (hi.mul_const _) differentiableAt_id]
  · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      fderiv_id, fderiv_const, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
      projectionDerivative]
    rw [fderiv_mul_const hi]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_inner_apply ℝ (f := fun y : State N => y)
      (g := fun _ : State N => v) differentiableAt_id (differentiableAt_const v)]
    simp only [fderiv_fun_id, fderiv_const_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, inner_zero_right, zero_add, add_zero]
    simp only [div_eq_mul_inv, neg_smul]
    module

theorem projection_norm_le_onSphere {N : ℕ} (hN : N ≠ 0) (x v : State N)
    (hx : OnSphere x) : ‖projection x v‖ ≤ ‖v‖ := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hh := projection_inner_self x v
  change ⟪x, x⟫_ℝ = N at hx
  rw [hx] at hh
  have hsq : ‖projection x v‖ ^ 2 = ‖v‖ ^ 2 - ⟪x, v⟫_ℝ ^ 2 / N := by
    simp only [real_inner_self_eq_norm_sq] at hh
    field_simp at hh ⊢
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    (by rw [hsq]; exact sub_le_self _ (div_nonneg (sq_nonneg _) hn.le))

theorem noiseColumn_norm_le_onSphere {N : ℕ} (hN : N ≠ 0) (x : State N)
    (hx : OnSphere x) (j : Fin N) : ‖noiseColumn x j‖ ≤ Real.sqrt 2 := by
  rw [noiseColumn, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h := projection_norm_le_onSphere hN x (basisVector j) hx
  have hb : ‖basisVector j‖ = 1 := by simp [basisVector]
  rw [hb] at h
  simpa using mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg 2)

theorem noiseCoordinate_norm_le_onSphere {N : ℕ} (hN : N ≠ 0) (x : State N)
    (hx : OnSphere x) (i j : Fin N) : ‖(noiseColumn x j) i‖ ≤ Real.sqrt 2 :=
  (PiLp.norm_apply_le (noiseColumn x j) i).trans
    (noiseColumn_norm_le_onSphere hN x hx j)

open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Genuine standard coordinate Brownian data in the complete driving
filtration. In particular, independence is imposed on whole coordinate paths;
equal coordinates would not satisfy this definition. The filtration may
already contain the independent initial point and disorder. -/
structure BrownianDriver (N : ℕ) (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) where
  coordinate : Fin N → ℝ≥0 → Ω → ℝ
  brownian : ∀ i, IsBrownianMotion (coordinate i) P
  filtered : ∀ i, IsFilteredPreBrownian (coordinate i) 𝓕 P
  independent : iIndepFun (fun i ω => fun t => coordinate i t ω) P
  jointFiltered : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap
      (fun ω i => coordinate i t ω - coordinate i s ω) inferInstance) (𝓕 s) P

omit [IsProbabilityMeasure P] in
theorem BrownianDriver.coordinateStronglyMeasurable (D : BrownianDriver N P 𝓕)
    (i : Fin N) (t : ℝ≥0) : StronglyMeasurable (D.coordinate i t) :=
  ((D.filtered i).stronglyAdapted t).mono (𝓕.le t)

@[expose] def noiseCoefficient (X : ℝ≥0 → Ω → State N) (i j : Fin N) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (noiseColumn (X t ω) j) i

theorem stronglyAdapted_noiseCoefficient (X : ℝ≥0 → Ω → State N)
    (hX : StronglyAdapted 𝓕 X) (i j : Fin N) :
    StronglyAdapted 𝓕 (noiseCoefficient X i j) := by
  intro t
  exact ((continuous_noiseCoordinate i j).measurable.comp (hX t).measurable).stronglyMeasurable

omit [MeasurableSpace Ω] in
theorem continuous_noiseCoefficient (X : ℝ≥0 → Ω → State N)
    (hX : ∀ ω, Continuous (fun t => X t ω)) (i j : Fin N) (ω : Ω) :
    Continuous (fun t => noiseCoefficient X i j t ω) :=
  (continuous_noiseCoordinate i j).comp (hX ω)

/-- Local square integrability is the usual integrability condition needed
to interpret an Itô SDE; it contains no sphere or global boundedness assertion. -/
@[expose] def LocallySquareIntegrableNoise (X : ℝ≥0 → Ω → State N) : Prop :=
  ∀ (i j : Fin N) (T : ℝ≥0),
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (noiseCoefficient X i j) T)
      2 (nonnegativeLebesgueMeasure.prod P)

@[expose] def noisePredictable (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ ω, Continuous (fun t => X t ω))
    (hXi : LocallySquareIntegrableNoise (P := P) X)
    (i j : Fin N) (T : ℝ≥0) : PredictableProcessL2 𝓕 P :=
  ⟨(hXi i j T).toLp _,
    (FourPapersCommon.stronglyMeasurable_continuousAdaptedTimeCut 𝓕
      (noiseCoefficient X i j) (stronglyAdapted_noiseCoefficient X hXa i j)
      (continuous_noiseCoefficient X hXc i j) T).aestronglyMeasurable.congr
        (hXi i j T).coeFn_toLp.symm⟩

/-- The actual isometrically constructed Itô integral, summed over all
independent coordinates. Every coefficient remains adapted to `𝓕`. -/
@[expose] def coordinateNoiseIntegral (D : BrownianDriver N P 𝓕)
    (X : ℝ≥0 → Ω → State N)
    (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ ω, Continuous (fun t => X t ω))
    (hXi : LocallySquareIntegrableNoise (P := P) X)
    (i : Fin N) (T : ℝ≥0) : RandomL2 P :=
  ∑ j : Fin N, FourPapersCommon.FilteredBrownian.naturalItoIntegral
    (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j)
    (D.filtered j) (noisePredictable X hXa hXc hXi i j T)

/-- Coordinate integral-equation semantics for the finite-N multiplicative
noise SDE. This is a definition of a solution, not an existence theorem.
Adaptedness, continuity and local integrability are standard solution
regularity. Sphere invariance and nonexplosion are absent from the premises. -/
@[expose] def IsStrongSolutionOn (β : ℝ) (gradient : State N → State N)
    (D : BrownianDriver N P 𝓕) (initial : Ω → State N)
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  ∃ (hXa : StronglyAdapted 𝓕 X) (hXc : ∀ ω, Continuous (fun t => X t ω))
    (hXi : LocallySquareIntegrableNoise (P := P) X),
    ∀ t : ℝ≥0, t ≤ T → ∀ i : Fin N, ∀ᵐ ω ∂P,
      (X t ω) i = (initial ω) i +
        (∫ s in (0 : ℝ)..(t : ℝ), (drift β gradient (X s.toNNReal ω)) i) +
        (coordinateNoiseIntegral D X hXa hXc hXi i t : Ω → ℝ) ω

end SphericalAging.HardSphereDynamics
