-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PalomarSixClassDefinitions
public import SlowEquilibration.CuspSourceDefinitions
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section
noncomputable section
namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace
attribute [local instance] Classical.propDecidable

/-- The unit spin and its actual Gibbs mean. -/
def spin {N : ℕ} (x : Vector N) : Vector N := (Real.sqrt (N : ℝ))⁻¹ • x

def spinMean {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) : Vector N := ∫ x, spin x ∂gibbsLaw μ β J

def centeredSpinCoordinate {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (i : Fin N) (x : Vector N) : ℝ :=
  spin x i - spinMean μ β J i

/-- Actual Gibbs L² class; the fallback is unused in positive dimensions. -/
def centeredSpinL2 {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (i : Fin N) : Lp ℝ 2 (gibbsLaw μ β J) :=
  if h : MemLp (centeredSpinCoordinate μ β J i) 2 (gibbsLaw μ β J)
  then h.toLp (centeredSpinCoordinate μ β J i) else 0

/-- An eigenfunction of the physical heat semigroup, characterized directly
by integration against its transition laws. -/
def HeatEigenfunction {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (lam : ℝ) (u : Lp ℝ 2 (gibbsLaw μ β J)) : Prop :=
  ∀ t : ℝ≥0, (fun x => ∫ y, u y ∂transitionLaw (field μ J) β t x)
    =ᵐ[gibbsLaw μ β J] (fun x => Real.exp (-(t : ℝ)*lam)*u x)

/-- The closed positive spectral subspace for the interval (0,Λ]. -/
def lowSpectralSubspace {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (Λ : ℝ) : Submodule ℝ (Lp ℝ 2 (gibbsLaw μ β J)) :=
  (Submodule.span ℝ {u | ∃ lam : ℝ, 0 < lam ∧ lam ≤ Λ ∧ HeatEigenfunction μ β J lam u}).topologicalClosure

instance lowSpectralSubspace_hasOrthogonalProjection {N : ℕ} (μ : FiniteMixture)
    (β : ℝ) (J : Disorder N μ.maxDegree) (Λ : ℝ) :
    (lowSpectralSubspace μ β J Λ).HasOrthogonalProjection := by
  let : CompleteSpace (lowSpectralSubspace μ β J Λ) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- Squared norm of the genuine componentwise positive spectral projection. -/
def spinProjectionMass {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (Λ : ℝ) : ℝ :=
  ∑ i : Fin N, ‖(lowSpectralSubspace μ β J Λ).starProjection (centeredSpinL2 μ β J i)‖^2

/-- The joint law of stationary endpoints at times zero and t. -/
def stationaryJointLaw {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (t : ℝ≥0) : Measure (Vector N × Vector N) :=
  (gibbsLaw μ β J).bind (fun x => (transitionLaw (field μ J) β t x).map (Prod.mk x))

def connectedSpinCorrelation {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (t : ℝ≥0) : ℝ :=
  (∫ z, inner ℝ z.1 z.2/(N : ℝ) ∂stationaryJointLaw μ β J t) - ‖spinMean μ β J‖^2

/-- Endpoint mutual information, with natural logarithms. Stationarity
identifies both marginals with the actual Gibbs law. -/
def stationaryInformation {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (t : ℝ≥0) : ℝ≥0∞ :=
  InformationTheory.klDiv (stationaryJointLaw μ β J t) ((gibbsLaw μ β J).prod (gibbsLaw μ β J))

def PersistentMemoryConclusions {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (κ γ a c C : ℝ) : Prop :=
  SlowEquilibrationCuspSource.rayleighEigenvalue (gibbsLaw μ β J)
      (Nat.floor (Real.exp (κ*N))) ≤ Real.exp (-(2*γ)*N) ∧
  (∃ X : Set (Vector N), MeasurableSet X ∧ X ⊆ {x | OnSphere x} ∧
    1-C*Real.exp (-a*N) ≤ (gibbsLaw μ β J).real X ∧
    ∀ x ∈ X, ∀ t ≤ exponentialHorizon γ N,
      1-C*Real.exp (-a*N) ≤ totalVariation (transitionLaw (field μ J) β t x) (gibbsLaw μ β J)) ∧
  (∀ t : ℝ≥0, 0 < t → t ≤ exponentialHorizon γ N →
    ENNReal.ofReal (c*N) ≤ stationaryInformation μ β J t)

/-- All five literal finite-mixture memory conclusions. -/
def MemoryConclusions {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (b κ γ a c C : ℝ) : Prop :=
  PersistentMemoryConclusions μ β J κ γ a c C ∧
  b ≤ spinProjectionMass μ β J (Real.exp (-(2*γ)*N)) ∧
  ∀ t ≤ exponentialHorizon γ N, b ≤ connectedSpinCorrelation μ β J t

end SlowEquilibrationCondensedSource
