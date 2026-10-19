-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteGibbs
public import SlowEquilibration.SphericalC2Operator

/-! Actual form, weak generator and spectral semigroup on the literal
infinite-series Gibbs L² space. Transport uses the proved equality of measures,
so it does not assume a realization, spectrum, or operator identity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory Set Filter SphericalModel SphericalForm
open scoped Topology InnerProductSpace ENNReal NNReal
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LawTransport
variable {X : Type*} [MeasurableSpace X] {ν η : Measure X}

def vector (h : ν=η) (u : Lp ℝ 2 ν) : Lp ℝ 2 η := by cases h; exact u

def isometry (h : ν=η) : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 η := by
  cases h
  exact LinearIsometryEquiv.refl ℝ _

theorem isometry_apply (h : ν=η) (u : Lp ℝ 2 ν) : isometry h u=vector h u := by cases h; rfl

def clm (h : ν=η) (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    Lp ℝ 2 η →L[ℝ] Lp ℝ 2 η := by cases h; exact T

def pmap (h : ν=η) (T : Lp ℝ 2 ν →ₗ.[ℝ] Lp ℝ 2 ν) :
    Lp ℝ 2 η →ₗ.[ℝ] Lp ℝ 2 η := by cases h; exact T

def basis (h : ν=η) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 ν)) : HilbertBasis ℕ ℝ (Lp ℝ 2 η) where
  repr := (isometry h).symm.trans b.repr

theorem basis_apply (h : ν=η) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 ν)) (j : ℕ) :
    basis h b j=vector h (b j) := by
  change isometry h (b j)=_
  exact isometry_apply h (b j)

theorem vector_smul (h : ν=η) (c : ℝ) (u : Lp ℝ 2 ν) :
    vector h (c • u)=c • vector h u := by cases h; rfl

theorem vector_neg (h : ν=η) (u : Lp ℝ 2 ν) :
    vector h (-u) = -vector h u := by cases h; rfl

theorem clm_compact (h : ν=η) (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : IsCompactOperator T) : IsCompactOperator (clm h T) := by cases h; exact hT

theorem pmap_selfAdjoint (h : ν=η) (T : Lp ℝ 2 ν →ₗ.[ℝ] Lp ℝ 2 ν)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (pmap h T) := by cases h; exact hT

theorem pmap_nonneg (h : ν=η) (T : Lp ℝ 2 ν →ₗ.[ℝ] Lp ℝ 2 ν)
    (hT : ∀ u : T.domain,0 ≤ inner ℝ (T u) (u : Lp ℝ 2 ν)) :
    ∀ u : (pmap h T).domain,0 ≤ inner ℝ (pmap h T u) (u : Lp ℝ 2 η) := by cases h; exact hT

theorem pmap_domain (h : ν=η) (T : Lp ℝ 2 ν →ₗ.[ℝ] Lp ℝ 2 ν)
    (R : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hT : T.domain=R.range) :
    (pmap h T).domain=(clm h R).range := by cases h; exact hT

theorem pmap_action (h : ν=η) (T : Lp ℝ 2 ν →ₗ.[ℝ] Lp ℝ 2 ν)
    (u v : Lp ℝ 2 ν) (he : ∃ hu : u∈T.domain,T ⟨u,hu⟩=v) :
    ∃ hu : vector h u∈(pmap h T).domain,
      pmap h T ⟨vector h u,hu⟩=vector h v := by cases h; exact he

end LawTransport

/-- L² of the original, literal series Gibbs probability. -/
abbrev LiteralGibbsL2 (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) (β : ℝ) :=
  Lp ℝ 2 (gibbsLaw (n+1) β (field μ J))

/-- The actual weak resolvent of the spherical gradient form, expressed on
L² of the original series Gibbs law. -/
def literalL2Resolvent (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    LiteralGibbsL2 n μ J β →L[ℝ] LiteralGibbsL2 n μ J β :=
  LawTransport.clm (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (sphericalL2Resolvent (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous)

/-- The actual self-adjoint nonnegative generator of the completed form,
with the actual weak-resolvent domain, under the original Gibbs law. -/
def literalWeakGenerator (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    LiteralGibbsL2 n μ J β →ₗ.[ℝ] LiteralGibbsL2 n μ J β :=
  LawTransport.pmap (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (sphericalGenerator (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous)

theorem literalWeakGenerator_selfAdjoint (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    IsSelfAdjoint (literalWeakGenerator n μ J hJ β) :=
  LawTransport.pmap_selfAdjoint _ _ (sphericalGenerator_selfAdjoint (by omega) β _ _)

theorem literalWeakGenerator_isClosed (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    (literalWeakGenerator n μ J hJ β).IsClosed :=
  (literalWeakGenerator_selfAdjoint n μ J hJ β).isClosed

theorem literalWeakGenerator_nonneg (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (u : (literalWeakGenerator n μ J hJ β).domain) :
    0 ≤ inner ℝ (literalWeakGenerator n μ J hJ β u) (u : LiteralGibbsL2 n μ J β) :=
  LawTransport.pmap_nonneg _ _ (sphericalGenerator_nonneg (by omega) β _ _) u

theorem literalWeakGenerator_domain (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    (literalWeakGenerator n μ J hJ β).domain=(literalL2Resolvent n μ J hJ β).range :=
  LawTransport.pmap_domain _ _ _ rfl

theorem literalL2Resolvent_compact (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    IsCompactOperator (literalL2Resolvent n μ J hJ β) :=
  LawTransport.clm_compact _ _ (sphericalL2Resolvent_compact (by omega) β _ _)

/-- An actual continuous observable as an element of literal Gibbs L². -/
def literalGibbsToL2 (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) (β : ℝ) (f : Vector (n+1) → ℝ) (hf : Continuous f) :
    LiteralGibbsL2 n μ J β :=
  LawTransport.vector (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (gibbsToL2 (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous f hf)

/-- The original Gibbs-space operator acts on every true C² test as the
negative literal spherical differential generator. -/
theorem literalWeakGenerator_C2 (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ hdom : literalGibbsToL2 n μ J hJ β f hf.continuous ∈
        (literalWeakGenerator n μ J hJ β).domain,
      literalWeakGenerator n μ J hJ β ⟨literalGibbsToL2 n μ J hJ β f hf.continuous,hdom⟩ =
        (-1:ℝ) • literalGibbsToL2 n μ J hJ β (rotationGenerator (n+1) β (regularAmbientField n μ J) f)
          (rotationGenerator_continuous β ((regularAmbientField_contDiff n μ J).of_le (by norm_num)) hf) := by
  have h := LawTransport.pmap_action (literal_gibbsLaw_eq_regular n μ β J hJ).symm _ _ _
    (sphericalGenerator_C2 (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      ((regularAmbientField_contDiff n μ J).of_le (by norm_num)) f hf)
  simpa only [literalWeakGenerator,literalGibbsToL2,neg_one_smul,LawTransport.vector_neg] using h

/-- The actual normalized spectral data transported to literal Gibbs L².
Its eigenvalues are exactly those already used by the infinite spectral bounds. -/
def literalSpectralSemigroupData (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    SpectralSemigroup.Data (LiteralGibbsL2 n μ J β) where
  basis := LawTransport.basis (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (infiniteSpectralData n hn β μ J).basis
  eigenvalue := (infiniteSpectralData n hn β μ J).eigenvalue
  eigenvalue_nonneg := (infiniteSpectralData n hn β μ J).eigenvalue_nonneg

theorem literalSpectral_eigenvalue (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (j : ℕ) :
    (literalSpectralSemigroupData n hn μ J hJ β).eigenvalue j =
      (infiniteSpectralData n hn β μ J).eigenvalue j :=
  rfl

/-- These are actual eigenvectors of the original Gibbs-space weak
operator, rather than an unrelated diagonal operator. -/
theorem literalWeakGenerator_eigen (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (j : ℕ) :
    ∃ hdom : (literalSpectralSemigroupData n hn μ J hJ β).basis j ∈
        (literalWeakGenerator n μ J hJ β).domain,
      literalWeakGenerator n μ J hJ β
        ⟨(literalSpectralSemigroupData n hn μ J hJ β).basis j,hdom⟩ =
      (infiniteSpectralData n hn β μ J).eigenvalue j •
        (literalSpectralSemigroupData n hn μ J hJ β).basis j := by
  have h := LawTransport.pmap_action (literal_gibbsLaw_eq_regular n μ β J hJ).symm _ _ _
    ((infiniteSpectralData n hn β μ J).generator_eigen j)
  simpa only [literalWeakGenerator,literalSpectralSemigroupData,LawTransport.basis_apply,LawTransport.vector_smul] using h

/-- The genuine form spectral semigroup on L² of the original Gibbs law.
Identification with the physical transition kernel is a separate statement. -/
def literalFormSemigroup (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (t : ℝ≥0) :=
  (literalSpectralSemigroupData n hn μ J hJ β).P t

theorem literalFormSemigroup_selfAdjoint (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (t : ℝ≥0) :
    IsSelfAdjoint (literalFormSemigroup n hn μ J hJ β t) :=
  (literalSpectralSemigroupData n hn μ J hJ β).P_isSelfAdjoint t

theorem literalFormSemigroup_contractive (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (t : ℝ≥0)
    (u : LiteralGibbsL2 n μ J β) : ‖literalFormSemigroup n hn μ J hJ β t u‖≤‖u‖ :=
  (literalSpectralSemigroupData n hn μ J hJ β).P_norm_le t u

theorem literalFormSemigroup_add (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (s t : ℝ≥0) :
    literalFormSemigroup n hn μ J hJ β (s+t) =
      (literalFormSemigroup n hn μ J hJ β s).comp (literalFormSemigroup n hn μ J hJ β t) :=
  (literalSpectralSemigroupData n hn μ J hJ β).P_add s t

theorem literalFormSemigroup_continuous (n : ℕ) (hn : 1≤n) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (u : LiteralGibbsL2 n μ J β) : Continuous (fun t => literalFormSemigroup n hn μ J hJ β t u) :=
  (literalSpectralSemigroupData n hn μ J hJ β).P_apply_continuous u

end SlowEquilibration.SphericalInfiniteModel
