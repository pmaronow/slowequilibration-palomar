-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagSlabTails

/-! Concrete statement objects for the conditional condensed-phase theorem.
The declarations in `SlowEquilibrationCondensedSource` are repeated verbatim in
the Mathlib-only Challenge. Their connection with the development is proved below. -/

@[expose] public section
noncomputable section

namespace SlowEquilibrationCondensedSource
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

/-- A nonzero finite covariance with nonnegative coefficients and no degrees below two. -/
structure FiniteMixture where
  coeff : ℕ →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_below_two : ∀ p, p < 2 → coeff p = 0
  nonzero : coeff ≠ 0

/-- The smallest degree with a positive coefficient; the support is nonempty. -/
def FiniteMixture.minDegree (μ : FiniteMixture) : ℕ :=
  μ.coeff.support.min' (Finsupp.support_nonempty_iff.mpr μ.nonzero)

/-- The largest supported degree, used to index the finite tensor product. -/
def FiniteMixture.maxDegree (μ : FiniteMixture) : ℕ :=
  μ.coeff.support.max' (Finsupp.support_nonempty_iff.mpr μ.nonzero)

/-- The covariance polynomial ξ(r)=Σ cₚrᵖ, on all real overlaps. -/
def FiniteMixture.xi (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ∑ p ∈ μ.coeff.support, μ.coeff p * r ^ p

/-- The ambient real Euclidean state space in dimension N. -/
abbrev Vector (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Allowed ordered tensor degrees 2,...,P, including degrees with zero coefficient. -/
abbrev Degree (P : ℕ) := {p : Fin (P + 1) // 2 ≤ p.val}

/-- Independent ordered tensors, including repeated coordinate indices, in each degree. -/
abbrev Disorder (N P : ℕ) := (p : Degree P) → ((Fin p.val.val → Fin N) → ℝ)

/-- Product law of independent standard real Gaussian entries in every ordered tensor. -/
def disorderLaw (N P : ℕ) : Measure (Disorder N P) :=
  Measure.pi (fun p : Degree P =>
    Measure.pi (fun _ : Fin p.val.val → Fin N => gaussianReal 0 1))

/-- The sphere of radius √N, written without a square-root convention at N=0. -/
def OnSphere {N : ℕ} (x : Vector N) : Prop := inner ℝ x x = (N : ℝ)

/-- The Hamiltonian Σₚ√cₚ N^{−(p−1)/2} Σᵢ Jᵢ xᵢ₁⋯xᵢₚ, with positive Gibbs sign. -/
def field {N : ℕ} (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (x : Vector N) : ℝ :=
  ∑ p : Degree μ.maxDegree, Real.sqrt (μ.coeff p.val.val) *
    ((N : ℝ) ^ (-((p.val.val - 1 : ℕ) : ℝ) / 2) *
      ∑ I : Fin p.val.val → Fin N, J p I * ∏ k : Fin p.val.val, x (I k))

/-- Normalized uniform sphere law obtained by radial projection of standard Gaussian measure.
At N=0 the map sends the unique vector to zero; all limits use positive dimensions. -/
def sphereLaw (N : ℕ) : Measure (Vector N) :=
  (stdGaussian (Vector N)).map (fun x : Vector N => (Real.sqrt (N : ℝ) / ‖x‖) • x)

/-- The partition integral against normalized uniform surface measure; H is an ambient field. -/
def partition (N : ℕ) (β : ℝ) (H : Vector N → ℝ) : ℝ :=
  ∫ x, Real.exp (β * H x) ∂sphereLaw N

/-- Gibbs measure e^{βH}/Z times uniform sphere measure, for an ambient field H. -/
def gibbsMeasure (N : ℕ) (β : ℝ) (H : Vector N → ℝ) : Measure (Vector N) :=
  (sphereLaw N).withDensity (fun x =>
    ENNReal.ofReal (Real.exp (β * H x) / partition N β H))

/-- The finite-mixture Gibbs law; positive β favors high Hamiltonian values. -/
def gibbsLaw {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) : Measure (Vector N) :=
  gibbsMeasure N β (field μ J)

/-- Disorder-averaged log partition per ambient dimension; real division fixes N=0. -/
def quenchedPressure (N : ℕ) (μ : FiniteMixture) (β : ℝ) : ℝ :=
  (∫ J : Disorder N μ.maxDegree, Real.log (partition N β (field μ J))
    ∂disorderLaw N μ.maxDegree) / (N : ℝ)

/-- A probability law's compact support cutoff q in [0,1); probability is imposed separately. -/
def HasCutoff (ζ : Measure ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ q < 1 ∧ ∀ᵐ s ∂ζ, s ∈ Icc (0 : ℝ) q

/-- Integrated distribution function x̂(t)=∫(1−max(t,s))dζ(s), for admissible overlap laws. -/
def xHat (ζ : Measure ℝ) (t : ℝ) : ℝ := ∫ s, 1 - max t s ∂ζ

/-- Crisanti–Sommers pressure functional at any support cutoff q<1, with factor 1/2. -/
def csFunctional (β : ℝ) (η : ℝ → ℝ) (ζ : Measure ℝ) (q : ℝ) : ℝ :=
  (β ^ 2 * (η 1 - ∫ s, η s ∂ζ) +
    (∫ t in (0 : ℝ)..q, (xHat ζ t)⁻¹) + Real.log (1 - q)) / 2

/-- The CS variational minimum over all probability overlap laws supported in [0,q], q<1.
The cutoff is quantified rather than chosen; the functional is independent of a valid cutoff. -/
def csMinimum (μ : FiniteMixture) (β : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ ζ : Measure ℝ, IsProbabilityMeasure ζ ∧
    ∃ q : ℝ, HasCutoff ζ q ∧ v = csFunctional β μ.xi ζ q}

/-- Chen's Parisi formula for every nonzero finite mixture of degrees at least two and β≥0.
This explicit literature premise identifies the actual Gaussian quenched limit with the CS minimum. -/
def Chen2013FiniteParisi : Prop :=
  ∀ (μ : FiniteMixture) (β : ℝ), 0 ≤ β →
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 (csMinimum μ β))

/-- Subag's Lemma 22 lower-tail premise at every positive deficit and every exponential rate.
The centering is the actual quenched pressure; β may be any real number. -/
def PressureLowerTails (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∀ t c : ℝ, 0 < t → 0 < c → ∀ᶠ N : ℕ in atTop,
    (disorderLaw N μ.maxDegree).real
      {J | Real.log (partition N β (field μ J)) / (N : ℝ) <
        quenchedPressure N μ β - t} ≤ Real.exp (-c * (N : ℝ))

/-- One-step overlap law xδ₀+(1−x)δQ; certificate weights and locations lie in (0,1). -/
def twoAtom (x Q : ℝ) : Measure ℝ :=
  ENNReal.ofReal x • Measure.dirac 0 + ENNReal.ofReal (1 - x) • Measure.dirac Q

/-- The strict-contact potential V(r)=∫₀ʳ(r−t)/x̂(t)²dt−β²ξ(r), on the real extension. -/
def potential (μ : FiniteMixture) (β x Q r : ℝ) : ℝ :=
  -(β ^ 2 * μ.xi r - ∫ t in (0 : ℝ)..r, (r - t) / (xHat (twoAtom x Q) t) ^ 2)

/-- Literal strict 1RSB scalar certificate: minimum degree ≥4, β>0, interior x,Q,
zero value and slope at Q, positivity off Q, and positive second derivative at Q. -/
def Certificate (μ : FiniteMixture) (β x Q : ℝ) : Prop :=
  4 ≤ μ.minDegree ∧ 0 < β ∧ x ∈ Ioo (0 : ℝ) 1 ∧ Q ∈ Ioo (0 : ℝ) 1 ∧
    potential μ β x Q Q = 0 ∧ deriv (potential μ β x Q) Q = 0 ∧
    (∀ r ∈ Ioo (0 : ℝ) 1, r ≠ Q → 0 < potential μ β x Q r) ∧
    0 < deriv (deriv (potential μ β x Q)) Q

end SlowEquilibrationCondensedSource

namespace SlowEquilibration.PalomarCondensed
open MeasureTheory Set Filter
open scoped Topology

/-- Repackage the canonical finite covariance without changing any coefficient. -/
def toLibrary (μ : SlowEquilibrationCondensedSource.FiniteMixture) : SlowEquilibration.FiniteMixture :=
  ⟨μ.coeff, μ.nonneg, μ.zero_below_two, μ.nonzero⟩

/-- Every library covariance has the identical standalone representation. -/
def ofLibrary (μ : SlowEquilibration.FiniteMixture) : SlowEquilibrationCondensedSource.FiniteMixture :=
  ⟨μ.coeff, μ.nonneg, μ.zero_below_two, μ.nonzero⟩

theorem toLibrary_ofLibrary (μ : SlowEquilibration.FiniteMixture) :
    toLibrary (ofLibrary μ) = μ := rfl

theorem ofLibrary_toLibrary (μ : SlowEquilibrationCondensedSource.FiniteMixture) : ofLibrary (toLibrary μ) = μ := rfl

theorem minDegree_eq (μ : SlowEquilibrationCondensedSource.FiniteMixture) : μ.minDegree = (toLibrary μ).minDegree := rfl
theorem maxDegree_eq (μ : SlowEquilibrationCondensedSource.FiniteMixture) : μ.maxDegree = (toLibrary μ).maxDegree := rfl
theorem xi_eq (μ : SlowEquilibrationCondensedSource.FiniteMixture) : μ.xi = (toLibrary μ).xi := rfl
theorem disorderLaw_eq (N P : ℕ) : SlowEquilibrationCondensedSource.disorderLaw N P = SphericalModel.disorderLaw N P := rfl
theorem onSphere_eq {N : ℕ} (x : SlowEquilibrationCondensedSource.Vector N) :
    SlowEquilibrationCondensedSource.OnSphere x = SphericalAging.HardSphereDynamics.OnSphere x := rfl
theorem field_eq {N : ℕ} (μ : SlowEquilibrationCondensedSource.FiniteMixture) (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) :
    SlowEquilibrationCondensedSource.field μ J = SphericalModel.fieldOfMixture (toLibrary μ) J := rfl
theorem sphereLaw_eq (N : ℕ) : SlowEquilibrationCondensedSource.sphereLaw N = SphericalModel.sphereLaw N := rfl
theorem partition_eq {N : ℕ} (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) :
    SlowEquilibrationCondensedSource.partition N β (SlowEquilibrationCondensedSource.field μ J) = SphericalModel.mixturePartition (toLibrary μ) β J := rfl
theorem gibbsMeasure_eq (N : ℕ) (β : ℝ) (H : SlowEquilibrationCondensedSource.Vector N → ℝ) :
    SlowEquilibrationCondensedSource.gibbsMeasure N β H = SphericalModel.gibbsLaw N β H := rfl
theorem gibbsLaw_eq {N : ℕ} (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ)
    (J : SlowEquilibrationCondensedSource.Disorder N μ.maxDegree) :
    SlowEquilibrationCondensedSource.gibbsLaw μ β J = SphericalModel.mixtureGibbsLaw (toLibrary μ) β J := rfl
theorem quenchedPressure_eq (N : ℕ) (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) :
    SlowEquilibrationCondensedSource.quenchedPressure N μ β = SphericalModel.quenchedPressure N (toLibrary μ) β := rfl
theorem hasCutoff_eq (ζ : Measure ℝ) (q : ℝ) :
    SlowEquilibrationCondensedSource.HasCutoff ζ q = CrisantiSommers.HasCutoff ζ q := rfl
theorem xHat_eq (ζ : Measure ℝ) : SlowEquilibrationCondensedSource.xHat ζ = CrisantiSommers.xHat ζ := rfl
theorem csFunctional_eq (β : ℝ) (η : ℝ → ℝ) (ζ : Measure ℝ) (q : ℝ) :
    SlowEquilibrationCondensedSource.csFunctional β η ζ q = CrisantiSommers.functional β η ζ q := rfl
theorem twoAtom_eq (x Q : ℝ) : SlowEquilibrationCondensedSource.twoAtom x Q = CrisantiSommers.twoAtom x Q := rfl
theorem potential_eq (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β x Q : ℝ) :
    SlowEquilibrationCondensedSource.potential μ β x Q = CSStructure.potential (toLibrary μ) β (CrisantiSommers.twoAtom x Q) := rfl

/-- The cutoff-free standalone infimum is the development's attained CS minimum. -/
theorem csMinimum_eq (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) :
    SlowEquilibrationCondensedSource.csMinimum μ β = CSParisiMeasure.variationalValue (toLibrary μ) β := by
  let m := CSParisiMeasure.canonicalMinimizer (toLibrary μ) β
  let S := {v : ℝ | ∃ ζ : Measure ℝ, IsProbabilityMeasure ζ ∧
    ∃ q : ℝ, SlowEquilibrationCondensedSource.HasCutoff ζ q ∧ v = SlowEquilibrationCondensedSource.csFunctional β μ.xi ζ q}
  have hmem : CSParisiMeasure.variationalValue (toLibrary μ) β ∈ S := by
    refine ⟨m.law, m.probability, m.cutoff, m.hasCutoff, ?_⟩
    rfl
  have hlo : ∀ v ∈ S, CSParisiMeasure.variationalValue (toLibrary μ) β ≤ v := by
    rintro v ⟨ζ, hζ, q, hq, rfl⟩
    let a : CrisantiSommers.Admissible := ⟨ζ, hζ, ⟨q, hq⟩⟩
    have h := CSParisiMeasure.canonicalMinimizer_isMinimizer (toLibrary μ) β a
    rw [a.value_eq β (toLibrary μ).xi hq] at h
    exact h
  exact le_antisymm (csInf_le ⟨_, hlo⟩ hmem) (le_csInf ⟨_, hmem⟩ hlo)

theorem chen_iff : SlowEquilibrationCondensedSource.Chen2013FiniteParisi ↔ SourceLiteratureParisi.Chen2013FiniteParisi := by
  constructor
  · intro h μ β hβ
    have hh := h (ofLibrary μ) β hβ
    rw [csMinimum_eq] at hh
    exact hh
  · intro h μ β hβ
    rw [csMinimum_eq]
    exact h (toLibrary μ) β hβ

theorem pressureLowerTails_iff (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β : ℝ) :
    SlowEquilibrationCondensedSource.PressureLowerTails μ β ↔ LiteratureSubagBandLowerComplete.PressureLowerTails (toLibrary μ) β := Iff.rfl

theorem certificate_iff (μ : SlowEquilibrationCondensedSource.FiniteMixture) (β x Q : ℝ) :
    SlowEquilibrationCondensedSource.Certificate μ β x Q ↔ SphericalTAPCertificate.Certificate (toLibrary μ) β x Q := by
  constructor
  · rintro ⟨hd, hβ, hx, hQ, hv, hdv, hp, hdd⟩
    exact ⟨hd, hβ, hx, hQ, hv, hdv, hp, hdd⟩
  · intro h
    exact ⟨h.min_degree, h.beta_pos, h.weight_range, h.overlap_range, h.contact_value,
      h.contact_derivative, h.positive_off_contact, h.contact_curvature⟩

end SlowEquilibration.PalomarCondensed
