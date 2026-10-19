-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Concrete, approved-library statement objects for the spectral cusp.
These definitions contain no spectral, stochastic, or asymptotic conclusion.
The eigenvalue is expressed by the standard smooth Rayleigh min-max formula
on the original Gaussian-series Gibbs measure. The equivalence with the
constructed self-adjoint differential spectrum is a separate proof obligation. -/
@[expose] public section
noncomputable section
namespace SlowEquilibrationCuspSource
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff

abbrev Vector (N : ℕ) := EuclideanSpace ℝ (Fin N)
abbrev TensorIndex (N p : ℕ) := Fin p → Fin N
abbrev Disorder (N : ℕ) := (p : ℕ) → (TensorIndex N (p+2) → ℝ)

def disorderLaw (N : ℕ) : Measure (Disorder N) :=
  Measure.infinitePi (fun p : ℕ =>
    Measure.pi (fun _ : TensorIndex N (p+2) => gaussianReal 0 1))

def covariance (c : ℕ → ℝ) (r : ℝ) : ℝ := ∑' p, c p*r^p

def A (c : ℕ → ℝ) (r : ℝ) : ℝ :=
  (1-r)*(∑' p : ℕ, ((p+2 : ℕ) : ℝ)*c (p+2)*r^p)

def Amax (c : ℕ → ℝ) : ℝ :=
  sSup ((fun r : ℝ => (1-r)*deriv (covariance c) r/r) '' Ioo (0:ℝ) 1)

def dynamicalThreshold (c : ℕ → ℝ) : ℝ := Real.sqrt ((Amax c)⁻¹)

def staticThreshold (c : ℕ → ℝ) : ℝ :=
  Real.sqrt (sInf ((fun r : ℝ => (-r-Real.log (1-r))/covariance c r) '' Ioo (0:ℝ) 1))

def globalMaximizers (c : ℕ → ℝ) : Set ℝ := {r | r∈Icc (0:ℝ) 1 ∧ A c r=Amax c}
def qD (c : ℕ → ℝ) : ℝ := sSup (globalMaximizers c)

/-- The original ordered tensor series, with its physical normalization. -/
def field {N : ℕ} (c : ℕ → ℝ) (J : Disorder N) (x : Vector N) : ℝ :=
  ∑' p : ℕ, Real.sqrt (c (p+2)) *
    ((N:ℝ)^(-(((p+2-1 : ℕ) : ℝ))/2) *
      ∑ I : TensorIndex N (p+2), J p I * ∏ k : Fin (p+2), x (I k))

/-- Normalized spherical surface measure, realized by Gaussian radial projection. -/
def sphereLaw (N : ℕ) : Measure (Vector N) :=
  (stdGaussian (Vector N)).map (fun x : Vector N => (Real.sqrt (N:ℝ)/‖x‖) • x)

def gibbsLaw {N : ℕ} (β : ℝ) (H : Vector N → ℝ) : Measure (Vector N) :=
  (sphereLaw N).withDensity (fun x => ENNReal.ofReal
    (Real.exp (β*H x)/(∫ y, Real.exp (β*H y) ∂sphereLaw N)))

/-- The literal intrinsic gradient, using the ambient Riesz derivative. -/
def sphericalGradient {N : ℕ} (f : Vector N → ℝ) (x : Vector N) : Vector N :=
  let g := (InnerProductSpace.toDual ℝ (Vector N)).symm (fderiv ℝ f x)
  g - (inner ℝ x g/(N:ℝ)) • x

/-- A genuine smooth trial subspace with positive L² norm for nonzero vectors. -/
def RayleighTrial {N : ℕ} (π : Measure (Vector N)) (k : ℕ) (b : ℝ) : Prop :=
  ∃ U : Submodule ℝ (Vector N → ℝ),
    FiniteDimensional ℝ U ∧ k < Module.finrank ℝ U ∧
    (∀ f∈U, ContDiff ℝ ∞ f) ∧
    (∀ f∈U, f≠0 → 0 < ∫ x, (f x)^2 ∂π) ∧
    (∀ f∈U, (∫ x, ‖sphericalGradient f x‖^2 ∂π) ≤ b*(∫ x, (f x)^2 ∂π))

/-- The standard Rayleigh min-max eigenvalue of the actual spherical form. -/
def rayleighEigenvalue {N : ℕ} (π : Measure (Vector N)) (k : ℕ) : ℝ :=
  sInf {b : ℝ | RayleighTrial π k b}

def physicalEigenvalue {N : ℕ} (c : ℕ → ℝ) (J : Disorder N) (β : ℝ) (k : ℕ) : ℝ :=
  rayleighEigenvalue (gibbsLaw β (field c J)) k

end SlowEquilibrationCuspSource
