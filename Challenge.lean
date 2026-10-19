module
public import Mathlib

/-! Independent mathematical statement of Theorem 1.2, Corollary 1.3,
and Theorems 1.4–1.7. The sole literature premise is Chen's finite-mixture
Parisi formula in the first three groups. All statement objects are defined
below using Mathlib only. The separate Solution identifies the heat-law
and Rayleigh definitions with the actual physical diffusion and spectrum.
The twelve selected proof placeholders cover exactly the six groups. -/

@[expose] public section
noncomputable section

/-- The elementary L² exponent fact, proved here to fix the same instance in every definition. -/
instance ColeHopfFoundation.ProbabilityTheory.StrongDual.instFact_one_le_two :
    Fact (1 ≤ (2 : ENNReal)) := ⟨by simp⟩

/- Reset only Lean's auxiliary-proof cache at the original module boundaries;
this preserves generated proof names without changing any declaration or kernel rule. -/
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

/-- A finite nonzero covariance with nonnegative coefficients and no constant or linear term. -/
structure FiniteMixture where
  coeff : ℕ →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_below_two : ∀ p, p < 2 → coeff p = 0
  nonzero : coeff ≠ 0

def FiniteMixture.minDegree (μ : FiniteMixture) : ℕ :=
  μ.coeff.support.min' (Finsupp.support_nonempty_iff.mpr μ.nonzero)

def FiniteMixture.maxDegree (μ : FiniteMixture) : ℕ :=
  μ.coeff.support.max' (Finsupp.support_nonempty_iff.mpr μ.nonzero)

/-- The literal covariance polynomial, defined at every real overlap. -/
def FiniteMixture.xi (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.coeff p * r ^ p

abbrev Vector (N : ℕ) := EuclideanSpace ℝ (Fin N)

abbrev Degree (P : ℕ) := {p : Fin (P + 1) // 2 ≤ p.val}

abbrev Disorder (N P : ℕ) := (p : Degree P) → ((Fin p.val.val → Fin N) → ℝ)

/-- Independent standard Gaussian entries in every ordered tensor, including repeated indices. -/
def disorderLaw (N P : ℕ) : Measure (Disorder N P) :=
  Measure.pi (fun p : Degree P =>
    Measure.pi (fun _ : Fin p.val.val → Fin N => gaussianReal 0 1))

def OnSphere {N : ℕ} (x : Vector N) : Prop := inner ℝ x x = (N : ℝ)

/-- The physical tensor Hamiltonian with coefficients √cₚ and normalization N^{−(p−1)/2}. -/
def field {N : ℕ} (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (x : Vector N) : ℝ :=
  ∑ p : Degree μ.maxDegree, Real.sqrt (μ.coeff p.val.val) *
    ((N : ℝ) ^ (-((p.val.val - 1 : ℕ) : ℝ) / 2) *
      ∑ I : Fin p.val.val → Fin N, J p I * ∏ k : Fin p.val.val, x (I k))

/-- Normalized sphere measure, realized by radial projection of a standard Gaussian. -/
def sphereLaw (N : ℕ) : Measure (Vector N) :=
  (stdGaussian (Vector N)).map (fun x : Vector N => (Real.sqrt (N : ℝ) / ‖x‖) • x)

/-- The actual partition integral against normalized uniform sphere measure. -/
def partition (N : ℕ) (β : ℝ) (H : Vector N → ℝ) : ℝ :=
  ∫ x, Real.exp (β * H x) ∂sphereLaw N

/-- The normalized positive-sign Gibbs density exp(βH)/Z against sphere measure. -/
def gibbsMeasure (N : ℕ) (β : ℝ) (H : Vector N → ℝ) : Measure (Vector N) :=
  (sphereLaw N).withDensity (fun x =>
    ENNReal.ofReal (Real.exp (β * H x) / partition N β H))

def gibbsLaw {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) : Measure (Vector N) :=
  gibbsMeasure N β (field μ J)

/-- The actual finite-dimensional disorder mean of log Z, divided by N. -/
def quenchedPressure (N : ℕ) (μ : FiniteMixture) (β : ℝ) : ℝ :=
  (∫ J : Disorder N μ.maxDegree, Real.log (partition N β (field μ J))
    ∂disorderLaw N μ.maxDegree) / (N : ℝ)

/-- Support in [0,q] for a deterministic q<1; the probability requirement is separate. -/
def HasCutoff (ζ : Measure ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ ∀ᵐ s ∂ζ, s ∈ Icc (0 : ℝ) q

/-- The integrated overlap distribution used by the Crisanti–Sommers functional. -/
def xHat (ζ : Measure ℝ) (t : ℝ) : ℝ := ∫ s, 1 - max t s ∂ζ

/-- The Crisanti–Sommers pressure functional, with the manuscript factor one half. -/
def csFunctional (β : ℝ) (η : ℝ → ℝ) (ζ : Measure ℝ) (q : ℝ) : ℝ :=
  (β ^ 2 * (η 1 - ∫ s, η s ∂ζ) +
    (∫ t in (0 : ℝ)..q, (xHat ζ t)⁻¹) + Real.log (1 - q)) / 2

/-- The CS variational infimum over probability laws supported in [0,q] for some q<1. -/
def csMinimum (μ : FiniteMixture) (β : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ ζ : Measure ℝ, IsProbabilityMeasure ζ ∧
    ∃ q : ℝ, HasCutoff ζ q ∧ v = csFunctional β μ.xi ζ q}

/-- Chen’s finite-mixture Parisi formula, stated universally as a theorem premise.
It is not a global axiom; all auxiliary mixtures are included. -/
def Chen2013FiniteParisi : Prop :=
  ∀ (μ : FiniteMixture) (β : ℝ), 0 ≤ β →
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 (csMinimum μ β))

def twoAtom (x Q : ℝ) : Measure ℝ :=
  ENNReal.ofReal x • Measure.dirac 0 + ENNReal.ofReal (1 - x) • Measure.dirac Q

/-- The literal strict-contact potential from its interval integral, not an assumed minimizer. -/
def potential (μ : FiniteMixture) (β x Q r : ℝ) : ℝ :=
  -(β ^ 2 * μ.xi r - ∫ t in (0 : ℝ)..r, (r - t) / (xHat (twoAtom x Q) t) ^ 2)

/-- Minimum degree≥4, β>0, interior one-step parameters, strict nondegenerate contact.
No probabilistic or dynamical conclusion is included in this scalar certificate. -/
def Certificate (μ : FiniteMixture) (β x Q : ℝ) : Prop :=
  4 ≤ μ.minDegree ∧ 0 < β ∧ x ∈ Ioo (0 : ℝ) 1 ∧ Q ∈ Ioo (0 : ℝ) 1 ∧
    potential μ β x Q Q = 0 ∧ deriv (potential μ β x Q) Q = 0 ∧
    (∀ r ∈ Ioo (0 : ℝ) 1, r ≠ Q → 0 < potential μ β x Q r) ∧
    0 < deriv (deriv (potential μ β x Q)) Q

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

attribute [-instance] ColeHopfFoundation.ProbabilityTheory.StrongDual.instFact_one_le_two

attribute [-instance] PolynormableSpace.continuousSMul

namespace SlowEquilibrationCondensedSource
open MeasureTheory Set
open scoped BigOperators Topology ContDiff NNReal

attribute [local instance] Classical.propDecidable

def heatProjection {N : ℕ} (x v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  v - (inner ℝ x v / (N : ℝ)) • x

def heatGradient {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm (fderiv ℝ f x)

/-- The intrinsic generator Δ_S+β∇_S H·∇_S on the radius-√N sphere.
The noise is √2 times tangent projection, so time has no extra factor one half. -/
def heatGenerator {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (f : EuclideanSpace ℝ (Fin N) → ℝ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  fderiv ℝ f x (β • heatProjection x (heatGradient H x) -
    (((N : ℝ) - 1) / (N : ℝ)) • x) +
    (1 / 2 : ℝ) * ∑ j : Fin N,
      fderiv ℝ (fderiv ℝ f) x
        (Real.sqrt 2 • heatProjection x (EuclideanSpace.single j 1))
        (Real.sqrt 2 • heatProjection x (EuclideanSpace.single j 1))

/-- The classical backward Cauchy problem for each compactly supported C² test.
The initial condition and positive-time PDE are imposed at every spherical point. -/
def IsHeatEvolution {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  (∀ t, ContDiff ℝ 2 (u t)) ∧ Continuous (Function.uncurry u) ∧
  Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin N) => heatGenerator H β (u p.1) p.2) ∧
  (∀ x, inner ℝ x x = (N : ℝ) → u 0 x = f x) ∧
  (∀ t, 0 < t → ∀ x, inner ℝ x x = (N : ℝ) →
    HasDerivAt (fun s => u s x) (heatGenerator H β (u t) x) t)

/-- A spherical probability law characterized by integrals of backward heat evolutions. -/
def IsTransitionLaw {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin N))
    (ν : Measure (EuclideanSpace ℝ (Fin N))) : Prop :=
  1 ≤ N ∧ inner ℝ x x = (N : ℝ) ∧ IsProbabilityMeasure ν ∧
  (∀ᵐ y ∂ν, inner ℝ y y = (N : ℝ)) ∧
  ∀ f : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
    ∃ u, IsHeatEvolution H β f u ∧ (∫ y, f y ∂ν) = u t x

/-- Choice of the uniquely characterized physical Langevin law. The point-mass fallback
is unused for finite-mixture fields, N≥1, and spherical initial points, as proved in Solution. -/
def transitionLaw {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → ℝ) (β : ℝ)
    (t : ℝ≥0) (x : EuclideanSpace ℝ (Fin N)) : Measure (EuclideanSpace ℝ (Fin N)) :=
  if h : ∃ ν, IsTransitionLaw H β t x ν then h.choose else Measure.dirac x

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

attribute [instance] PolynormableSpace.continuousSMul

attribute [instance] ColeHopfFoundation.ProbabilityTheory.StrongDual.instFact_one_le_two

namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Supremum of probability differences over all measurable events, with no factor two. -/
def totalVariation {α : Type*} [MeasurableSpace α] (ν π : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ B : Set α, MeasurableSet B ∧ r = |ν.real B - π.real B|}

def evolvedLaw {N : ℕ} (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : Measure (Vector N)) : Measure (Vector N) :=
  ν.bind (transitionLaw (field μ J) β t)

def distance {N : ℕ} (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : Measure (Vector N)) : ℝ :=
  totalVariation (evolvedLaw μ β t J ν) (gibbsLaw μ β J)

/-- The infimum over every real time in the full closed interval [0,T]. -/
def intervalDistance {N : ℕ} (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : Measure (Vector N)) : ℝ :=
  sInf ((fun t : ℝ => distance μ β t.toNNReal J ν) '' Icc 0 (T : ℝ))

def exponentialHorizon (γ : ℝ) (N : ℕ) : ℝ≥0 :=
  ⟨Real.exp ((N : ℝ)*γ), Real.exp_nonneg _⟩

/-- Convergence in disorder probability to distance one; dimensions n+2 are cofinal. -/
def uniformSeparation (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => (disorderLaw (n+2) μ.maxDegree).real
      {J | ε ≤ ‖intervalDistance μ β (exponentialHorizon γ (n+2)) J
        (sphereLaw (n+2))-1‖}) atTop (𝓝 0)

/-- Worst failure probability over prescribed spherical probability laws.
The supremum is outside the disorder probability. -/
def prescribedFailure (μ : FiniteMixture) (β γ ε : ℝ) (N : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ ν : ProbabilityMeasure (Vector N),
    (∀ᵐ x ∂ν.toMeasure, OnSphere x) ∧
    r = (disorderLaw N μ.maxDegree).real
      {J | intervalDistance μ β (exponentialHorizon γ N) J ν.toMeasure < 1-ε}}

def CondensedAndInitial (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  uniformSeparation μ β γ ∧
  (∀ ε : ℝ, 0 < ε → Tendsto (prescribedFailure μ β γ ε) atTop (𝓝 0)) ∧
  (∀ (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
      (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
      (J : ∀ n, Ω n → Disorder n μ.maxDegree)
      (ν : ∀ n, Ω n → ProbabilityMeasure (Vector n)),
      (∀ n, HasLaw (J n) (disorderLaw n μ.maxDegree) (P n)) →
      (∀ n, AEMeasurable (ν n) (P n)) →
      (∀ n, IndepFun
        (fun ω => fun x : {x : Vector n // OnSphere x} => field μ (J n ω) x)
        (ν n) (P n)) →
      (∀ n, 1 ≤ n → ∀ᵐ ω ∂P n, ∀ᵐ y ∂(ν n ω).toMeasure, OnSphere y) →
      ∀ ε : ℝ, 0 < ε → Tendsto
        (fun n => (P n).real {ω | intervalDistance μ β
          (exponentialHorizon γ n) (J n ω) (ν n ω).toMeasure < 1-ε})
        atTop (𝓝 0))

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

attribute [-instance] PolynormableSpace.continuousSMul

set_option backward.proofsInPublic true

namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal ProbabilityTheory

def fieldSphere (N : ℕ) : Set (Vector N) := Metric.sphere 0 (Real.sqrt N)

instance fieldSphere_compactSpace (N : ℕ) : CompactSpace (fieldSphere N) := by
  unfold fieldSphere
  infer_instance

theorem field_continuous {N : ℕ} (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    Continuous (field μ J) := by
  unfold field
  fun_prop

def restrictionLinear {N : ℕ} (μ : FiniteMixture) :
    Disorder N μ.maxDegree →ₗ[ℝ] C(fieldSphere N, ℝ) where
  toFun J := ⟨fun x => field μ J x.val, (field_continuous μ J).comp continuous_subtype_val⟩
  map_add' J K := by
    apply ContinuousMap.ext
    intro x
    simp only [field, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
    rfl
  map_smul' r J := by
    apply ContinuousMap.ext
    intro x
    change field μ (r • J) x.val = r * field μ J x.val
    unfold field
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc r, ← Finset.mul_sum]
    simp only [← mul_assoc, mul_comm _ r]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

def restrictionCLM {N : ℕ} (μ : FiniteMixture) :
    Disorder N μ.maxDegree →L[ℝ] C(fieldSphere N, ℝ) :=
  LinearMap.toContinuousLinearMap (restrictionLinear μ)

/-- The actual finite-dimensional image of the Hamiltonian restricted to the sphere. -/
abbrev SphereField (N : ℕ) (μ : FiniteMixture) :=
  LinearMap.range (restrictionCLM (N := N) μ).toLinearMap

instance sphereField_finiteDimensional (N : ℕ) (μ : FiniteMixture) :
    FiniteDimensional ℝ (SphereField N μ) := LinearMap.finiteDimensional_range _

def sphereFieldMap {N : ℕ} (μ : FiniteMixture) :
    Disorder N μ.maxDegree →L[ℝ] SphereField N μ := (restrictionCLM μ).rangeRestrict

def sphereFieldLaw (N : ℕ) (μ : FiniteMixture) : Measure (SphereField N μ) :=
  (disorderLaw N μ.maxDegree).map (sphereFieldMap μ)

/-- A continuous linear right inverse representing exactly the given spherical field.
Solution proves physical laws are independent of the chosen tensor representative. -/
def sphereLift {N : ℕ} (μ : FiniteMixture) :
    SphereField N μ →L[ℝ] Disorder N μ.maxDegree :=
  Classical.choose ((sphereFieldMap μ).exists_rightInverse_of_surjective
    (restrictionCLM μ).range_rangeRestrict)

abbrev MenuWeights (ι : Type*) [Fintype ι] :=
  {w : ι → ℝ // (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1}

def menuMixture {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (ν : ι → Measure X) (w : MenuWeights ι) : Measure X :=
  ∑ j, ENNReal.ofReal (w.val j) • ν j

/-- The joint infimum over all convex menu weights and all times in [0,T].
Weights may depend on the observed spherical Hamiltonian. -/
def sphereMenuDistance {N : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : FiniteMixture) (β : ℝ) (ν : ι → Measure (Vector N))
    (T : ℝ≥0) (H : SphereField N μ) : ℝ :=
  sInf {r : ℝ | ∃ w : MenuWeights ι, ∃ t : ℝ≥0, t ≤ T ∧
    r = distance μ β t (sphereLift μ H) (menuMixture ν w)}

def sphereIntervalDistance {N : ℕ} (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (κ : Kernel (SphereField N μ) (Vector N)) (H : SphereField N μ) : ℝ :=
  intervalDistance μ β T (sphereLift μ H) (κ H)

/-- Ordinary convergence in probability for dimension-dependent probability spaces. -/
def inProbability {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (d : ∀ N, Measure (Ω N)) (f : ∀ N, Ω N → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => (d N).real {ω | ε ≤ ‖f N ω - c‖}) atTop (𝓝 0)

/-- Extended KL is o(log N) in probability; infinite KL remains in every finite tail. -/
def littleLogInProbability {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (d : ∀ N, Measure (Ω N)) (I : ∀ N, Ω N → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto
    (fun N => (d N).real {ω | ENNReal.ofReal (ε * Real.log N) ≤ I N ω}) atTop (𝓝 0)

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

attribute [instance] PolynormableSpace.continuousSMul

namespace SlowEquilibrationCondensedSource
open Set MeasureTheory Filter
open scoped Topology BigOperators

def staticThreshold (ξ : ℝ → ℝ) : ℝ :=
  Real.sqrt (sInf ((fun r : ℝ => (-r-Real.log (1-r))/ξ r) '' Ioo 0 1))

def dynamicalThreshold (ξ : ℝ → ℝ) : ℝ :=
  Real.sqrt ((sSup ((fun r : ℝ => (1-r)*deriv ξ r/r) '' Ioo 0 1))⁻¹)

def qStar (ξ : ℝ → ℝ) (β : ℝ) : ℝ :=
  sSup {r : ℝ | r ∈ Ioo 0 1 ∧ 1 < β^2*((1-r)*deriv ξ r/r)}

def inverseSqrt (v : ℝ → ℝ) : ℝ → ℝ := fun r => (Real.sqrt (v r))⁻¹

def pureCovariance (p : ℕ) (hp : 2 ≤ p) : FiniteMixture where
  coeff := Finsupp.single p 1
  nonneg := by intro q; by_cases h : q=p <;> simp [h]
  zero_below_two := by
    intro q hq
    have h : q≠p := by omega
    simp [h]
  nonzero := by
    intro h
    have h' := congrArg (fun f : ℕ →₀ ℝ => f p) h
    simp at h'

structure ClassPerturbation (d P : ℕ) where
  coeff : ℕ →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_of_le : ∀ p, p ≤ d → coeff p = 0
  zero_of_gt : ∀ p, P < p → coeff p = 0
  even_supported : ∀ p ∈ coeff.support, Even p
  total_le_one : coeff.sum (fun _ c => c) ≤ 1

def ClassPerturbation.covariance {d P : ℕ} (b : ClassPerturbation d P)
    (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) : FiniteMixture where
  coeff := Finsupp.single d 1 + ε • b.coeff
  nonneg := by
    intro p
    apply add_nonneg
    · by_cases hp : p=d <;> simp [hp]
    · exact mul_nonneg hε (b.nonneg p)
  zero_below_two := by
    intro p hp
    have hpd : p≠d := by omega
    simp [hpd, b.zero_of_le p (by omega)]
  nonzero := by
    intro hz
    have h := congrArg (fun f : ℕ →₀ ℝ => f d) hz
    simp [b.zero_of_le d le_rfl] at h

def exampleParameter : ℝ := (45-24*Real.log 6)/(72*Real.log 6-85)
def exampleB : ℝ := exampleParameter*(10/9 : ℝ)^8
/-- The positive square-root branch of the exact inverse temperature in Corollary 1.3(d). -/
def exampleBeta : ℝ := Real.sqrt (15/((9/10 : ℝ)^3*(4+12*exampleParameter)))

theorem exampleB_pos : 0 < exampleB := by
  have harg : (1+(5/7 : ℝ))/(1-(5/7 : ℝ))=6 := by norm_num
  have hlo := Real.sum_range_le_log_div (x := (5/7 : ℝ))
    (by norm_num) (by norm_num) 1
  have hhi := Real.log_div_le_sum_range_add (x := (5/7 : ℝ))
    (by norm_num) (by norm_num) 6
  rw [harg] at hlo hhi
  norm_num [Finset.sum_range_succ] at hlo hhi
  have ht : 0 < exampleParameter := by
    unfold exampleParameter
    apply div_pos <;> linarith
  exact mul_pos ht (by positivity)

def exampleCovariance : FiniteMixture where
  coeff := Finsupp.single 4 1 + Finsupp.single 12 exampleB
  nonneg := by
    intro p
    apply add_nonneg
    · by_cases hp : p=4 <;> simp [hp]
    · by_cases hp : p=12 <;> simp [hp, exampleB_pos.le]
  zero_below_two := by
    intro p hp
    have h4 : p≠4 := by omega
    have h12 : p≠12 := by omega
    simp [h4,h12]
  nonzero := by
    intro h
    have h' := congrArg (fun f : ℕ →₀ ℝ => f 4) h
    norm_num at h'

/-- Uniform-start slow equilibration with one positive exponential time exponent. -/
def UniformConclusions (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ uniformSeparation μ β γ

universe u v

/-- The three retained initial-law clauses at the same uniform-start exponent.
The separate initial-point mutual-information corollary is omitted. -/
def SixInitialConclusions (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  let T := fun N => exponentialHorizon γ N
  CondensedAndInitial μ β γ ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (ν : ∀ N, ι N → Measure (Vector N)) [∀ N j, IsProbabilityMeasure (ν N j)],
      (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      inProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereMenuDistance μ β (ν N) (T N)) 1) ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
      (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
      (ν : ∀ N, R N → ι N → Measure (Vector N)),
      (∀ N j, Measurable (fun r => ν N r j)) →
      ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
      (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      inProbability (fun N => (ρ N).prod (sphereFieldLaw N μ))
        (fun N z => sphereMenuDistance μ β (ν N z.1) (T N) z.2) 1) ∧
  (∀ (κ : ∀ N, ProbabilityTheory.Kernel (SphereField N μ) (Vector N))
      [∀ N, ProbabilityTheory.IsMarkovKernel (κ N)],
      (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
      littleLogInProbability (fun N => sphereFieldLaw N μ)
        (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
      inProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereIntervalDistance μ β (T N) (κ N)) 1)

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

set_option backward.proofsInPublic false

attribute [-instance] ColeHopfFoundation.ProbabilityTheory.StrongDual.instFact_one_le_two

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

def field {N : ℕ} (c : ℕ → ℝ) (J : Disorder N) (x : Vector N) : ℝ :=
  ∑' p : ℕ, Real.sqrt (c (p+2)) *
    ((N:ℝ)^(-(((p+2-1 : ℕ) : ℝ))/2) *
      ∑ I : TensorIndex N (p+2), J p I * ∏ k : Fin (p+2), x (I k))

/-- Normalized sphere measure, realized by radial projection of a standard Gaussian. -/
def sphereLaw (N : ℕ) : Measure (Vector N) :=
  (stdGaussian (Vector N)).map (fun x : Vector N => (Real.sqrt (N:ℝ)/‖x‖) • x)

def gibbsLaw {N : ℕ} (β : ℝ) (H : Vector N → ℝ) : Measure (Vector N) :=
  (sphereLaw N).withDensity (fun x => ENNReal.ofReal
    (Real.exp (β*H x)/(∫ y, Real.exp (β*H y) ∂sphereLaw N)))

def sphericalGradient {N : ℕ} (f : Vector N → ℝ) (x : Vector N) : Vector N :=
  let g := (InnerProductSpace.toDual ℝ (Vector N)).symm (fderiv ℝ f x)
  g - (inner ℝ x g/(N:ℝ)) • x

/-- A smooth trial subspace of dimension greater than k, with positive L² norm
for nonzero functions and Rayleigh quotient bounded by b. -/
def RayleighTrial {N : ℕ} (π : Measure (Vector N)) (k : ℕ) (b : ℝ) : Prop :=
  ∃ U : Submodule ℝ (Vector N → ℝ),
    FiniteDimensional ℝ U ∧ k < Module.finrank ℝ U ∧
    (∀ f∈U, ContDiff ℝ ∞ f) ∧
    (∀ f∈U, f≠0 → 0 < ∫ x, (f x)^2 ∂π) ∧
    (∀ f∈U, (∫ x, ‖sphericalGradient f x‖^2 ∂π) ≤ b*(∫ x, (f x)^2 ∂π))

/-- The standard kth Rayleigh min-max value of the actual Gibbs Dirichlet form. -/
def rayleighEigenvalue {N : ℕ} (π : Measure (Vector N)) (k : ℕ) : ℝ :=
  sInf {b : ℝ | RayleighTrial π k b}

/-- The original Gaussian-series Gibbs min-max eigenvalue. Solution identifies it
with the spectrum of the unique self-adjoint differential-generator closure. -/
def physicalEigenvalue {N : ℕ} (c : ℕ → ℝ) (J : Disorder N) (β : ℝ) (k : ℕ) : ℝ :=
  rayleighEigenvalue (gibbsLaw β (field c J)) k

end SlowEquilibrationCuspSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

attribute [instance] ColeHopfFoundation.ProbabilityTheory.StrongDual.instFact_one_le_two

namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace
attribute [local instance] Classical.propDecidable

def spin {N : ℕ} (x : Vector N) : Vector N := (Real.sqrt (N : ℝ))⁻¹ • x

def spinMean {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) : Vector N := ∫ x, spin x ∂gibbsLaw μ β J

def centeredSpinCoordinate {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (i : Fin N) (x : Vector N) : ℝ :=
  spin x i - spinMean μ β J i

/-- The actual centered spin coordinate in Gibbs L². The zero fallback is unused
in positive dimensions because square integrability is proved in Solution. -/
def centeredSpinL2 {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (i : Fin N) : Lp ℝ 2 (gibbsLaw μ β J) :=
  if h : MemLp (centeredSpinCoordinate μ β J i) 2 (gibbsLaw μ β J)
  then h.toLp (centeredSpinCoordinate μ β J i) else 0

/-- An eigenfunction of the physical heat semigroup, using the transition integral.
The equality is in the actual Gibbs almost-everywhere sense at each time. -/
def HeatEigenfunction {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (lam : ℝ) (u : Lp ℝ 2 (gibbsLaw μ β J)) : Prop :=
  ∀ t : ℝ≥0, (fun x => ∫ y, u y ∂transitionLaw (field μ J) β t x)
    =ᵐ[gibbsLaw μ β J] (fun x => Real.exp (-(t : ℝ)*lam)*u x)

/-- The closed span of genuine semigroup eigenfunctions with eigenvalues in (0,Λ]. -/
def lowSpectralSubspace {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (Λ : ℝ) : Submodule ℝ (Lp ℝ 2 (gibbsLaw μ β J)) :=
  (Submodule.span ℝ {u | ∃ lam : ℝ, 0 < lam ∧ lam ≤ Λ ∧ HeatEigenfunction μ β J lam u}).topologicalClosure

instance lowSpectralSubspace_hasOrthogonalProjection {N : ℕ} (μ : FiniteMixture)
    (β : ℝ) (J : Disorder N μ.maxDegree) (Λ : ℝ) :
    (lowSpectralSubspace μ β J Λ).HasOrthogonalProjection := by
  let : CompleteSpace (lowSpectralSubspace μ β J Λ) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

/-- Sum of squared norms of the positive spectral projections of centered spin coordinates. -/
def spinProjectionMass {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (Λ : ℝ) : ℝ :=
  ∑ i : Fin N, ‖(lowSpectralSubspace μ β J Λ).starProjection (centeredSpinL2 μ β J i)‖^2

/-- The genuine stationary endpoint joint law at times zero and t. -/
def stationaryJointLaw {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (t : ℝ≥0) : Measure (Vector N × Vector N) :=
  (gibbsLaw μ β J).bind (fun x => (transitionLaw (field μ J) β t x).map (Prod.mk x))

def connectedSpinCorrelation {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (t : ℝ≥0) : ℝ :=
  (∫ z, inner ℝ z.1 z.2/(N : ℝ) ∂stationaryJointLaw μ β J t) - ‖spinMean μ β J‖^2

/-- Mutual information as extended KL of the joint law against its Gibbs marginal product. -/
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

/-- All five retained stationary-memory conclusions for the actual physical quantities. -/
def MemoryConclusions {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) (b κ γ a c C : ℝ) : Prop :=
  PersistentMemoryConclusions μ β J κ γ a c C ∧
  b ≤ spinProjectionMass μ β J (Real.exp (-(2*γ)*N)) ∧
  ∀ t ≤ exponentialHorizon γ N, b ≤ connectedSpinCorrelation μ β J t

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

set_option backward.proofsInPublic true

namespace SlowEquilibrationCondensedSource
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

theorem theorem_1_2 (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β := by
  sorry

theorem corollary_1_3_a (p : ℕ) (hp : 4≤p) {β : ℝ}
    (hβ : staticThreshold (fun r : ℝ => r^p)<β) (hChen : Chen2013FiniteParisi) :
    UniformConclusions (pureCovariance p (by omega)) β := by
  sorry

theorem corollary_1_3_b (μ : FiniteMixture) (hd : 4≤μ.minDegree) {β : ℝ}
    (hβ : staticThreshold μ.xi<β)
    (hξ : StrictConvexOn ℝ (Ioc 0 1) (inverseSqrt (deriv (deriv μ.xi))))
    (hChen : Chen2013FiniteParisi) : UniformConclusions μ β := by
  sorry

theorem corollary_1_3_b_degree_window (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    (hw : ((μ.minDegree : ℝ)+μ.maxDegree-5)^2 <
      6*((μ.minDegree : ℝ)-2)*((μ.maxDegree : ℝ)-2))
    {β : ℝ} (hβ : staticThreshold μ.xi<β) (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β := by
  sorry

theorem corollary_1_3_b_support (μ : FiniteMixture)
    (hs : ∀ p∈μ.coeff.support, p∈Finset.Icc 4 11)
    {β : ℝ} (hβ : staticThreshold μ.xi<β) (hChen : Chen2013FiniteParisi) :
    UniformConclusions μ β := by
  sorry

theorem corollary_1_3_c (d P : ℕ) (hd : 4≤d) (heven : Even d) (hdP : d<P)
    {β : ℝ} (hβ : staticThreshold (fun r : ℝ => r^d)<β)
    (hChen : Chen2013FiniteParisi) :
    ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ b : ClassPerturbation d P,
      b.coeff.sum (fun _ c => c)=1 → ∀ (ε : ℝ) (hε : 0<ε), ε<ε₀ →
        UniformConclusions (b.covariance (by omega) ε hε.le) β := by
  sorry

theorem corollary_1_3_d (hChen : Chen2013FiniteParisi) :
    UniformConclusions exampleCovariance exampleBeta := by
  sorry

theorem theorem_1_4_haar {N : ℕ} (hN : 1≤N) (μ : FiniteMixture) (β : ℝ)
    (T : ℝ≥0) (ν : ProbabilityMeasure (Vector N))
    (hν : ∀ᵐ x∂ν.toMeasure, OnSphere x) :
    (∫ J, 1-distance μ β T J ν.toMeasure ∂disorderLaw N μ.maxDegree) ≤
      ∫ J, 1-distance μ β T J (sphereLaw N) ∂disorderLaw N μ.maxDegree := by
  sorry

universe u v
theorem theorem_1_4 (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hChen : Chen2013FiniteParisi) :
    ∃ γ : ℝ, 0<γ ∧ SixInitialConclusions.{u,v} μ β γ := by
  sorry

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SlowEquilibrationCondensedSource
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
theorem theorem_1_5 (μ : FiniteMixture) {β b : ℝ}
    (hβd : dynamicalThreshold μ.xi < β) (hβs : β < staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) ((qStar μ.xi β)^2)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree), MeasurableSet Ω ∧
        (disorderLaw N μ.maxDegree).real Ωᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ J ∈ Ω, ∀ _hN : 2 ≤ N, MemoryConclusions μ β J b κ γ a c C := by
  sorry

theorem theorem_1_6 (μ : FiniteMixture) {β b : ℝ}
    (hβd : dynamicalThreshold μ.xi < β) (hβs : β < staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) (qStar μ.xi β)) :
    ∃ κ γ a c C : ℝ, 0 < κ ∧ 0 < γ ∧ 0 < a ∧ 0 < c ∧ 0 < C ∧
      (∀ᶠ N : ℕ in atTop, ∃ Ω₀ : Set (Disorder N μ.maxDegree), MeasurableSet Ω₀ ∧
        (disorderLaw N μ.maxDegree).real Ω₀ᶜ ≤ C*Real.exp (-a*N) ∧
        ∀ J ∈ Ω₀, ∀ _hN : 2 ≤ N, PersistentMemoryConclusions μ β J κ γ a c C) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∃ Ω : Set (Disorder N μ.maxDegree),
        MeasurableSet Ω ∧ (disorderLaw N μ.maxDegree).real Ωᶜ < η ∧
        ∀ J ∈ Ω, ∀ _hN : 2 ≤ N, MemoryConclusions μ β J b κ γ a c C) := by
  sorry

end SlowEquilibrationCondensedSource

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})

namespace SlowEquilibrationCuspSource
open Set Filter MeasureTheory
open scoped Topology
theorem theorem_1_7 (c : ℕ → ℝ)
    (hc : ∀ p,0≤c p) (hzero : ∀ p,p<2 → c p=0) (hne : c≠0)
    (hsum : Summable (fun p : ℕ => (p:ℝ)^(5/2:ℝ)*Real.sqrt (c p)))
    (hgap : SlowEquilibrationCuspSource.dynamicalThreshold c<
      SlowEquilibrationCuspSource.staticThreshold c) :
    (SlowEquilibrationCuspSource.globalMaximizers c).Finite ∧
      (SlowEquilibrationCuspSource.globalMaximizers c⊆Ioo (0:ℝ) 1) ∧
      SlowEquilibrationCuspSource.qD c∈SlowEquilibrationCuspSource.globalMaximizers c ∧
      (∀ q∈SlowEquilibrationCuspSource.globalMaximizers c,q≤SlowEquilibrationCuspSource.qD c) ∧
    ∃ m : ℕ,∃ a κ : ℝ,1 ≤ m ∧ 0<a ∧ 0<κ ∧
      ((fun y : ℝ => SlowEquilibrationCuspSource.A c (SlowEquilibrationCuspSource.qD c+y)/
          SlowEquilibrationCuspSource.Amax c-(1-a*y^(2*m)))
        =O[𝓝 (0:ℝ)] (fun y => y^(2*m+1))) ∧
      ∀ θ∈Ioo (0:ℝ) 1,∃ ε₀ : ℝ,0<ε₀ ∧
        ∀ β : ℝ,SlowEquilibrationCuspSource.dynamicalThreshold c<β →
          β^2*SlowEquilibrationCuspSource.Amax c-1<ε₀ →
        ∃ a' : ℝ,0<a' ∧ ∃ n₀ : ℕ,1≤n₀ ∧ ∀ n : ℕ,n₀≤n →
          ∃ Ω : Set (SlowEquilibrationCuspSource.Disorder (n+1)),MeasurableSet Ω ∧
            (SlowEquilibrationCuspSource.disorderLaw (n+1)).real Ωᶜ≤14*Real.exp (-a'*(n+1:ℕ)) ∧
            ∀ J∈Ω,SlowEquilibrationCuspSource.physicalEigenvalue c J β
                (Nat.floor (Real.exp (κ*(n+1:ℕ))))≤
              Real.exp (-(1-θ)*
                ((2*(m:ℝ)*SlowEquilibrationCuspSource.qD c)/
                  ((2*(m:ℝ)+1)*(1-SlowEquilibrationCuspSource.qD c))*a^(-1/(2*(m:ℝ))))*
                (β^2*SlowEquilibrationCuspSource.Amax c-1)^(1+((2*m:ℕ):ℝ)⁻¹)*(n+1:ℕ)) := by
  sorry

end SlowEquilibrationCuspSource
