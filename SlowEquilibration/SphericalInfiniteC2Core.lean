-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC2EssentialSelfAdjoint
public import SlowEquilibration.SphericalInfiniteOperators

/-! Essential self-adjointness of the literal C² differential restriction
under the original infinite-series Gibbs law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory Set SphericalModel SphericalForm
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

namespace LawTransport
variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
    {ν η : Measure X}

theorem vector_add (h : ν=η) (u v : Lp ℝ 2 ν) :
    vector h (u+v)=vector h u+vector h v := by cases h; rfl

def valueLinear (h : ν=η) (V : D →ₗ[ℝ] Lp ℝ 2 ν) : D →ₗ[ℝ] Lp ℝ 2 η where
  toFun f := vector h (V f)
  map_add' f g := by rw [map_add,vector_add]
  map_smul' c f := by rw [map_smul,vector_smul]; rfl

def valueSubmodule (h : ν=η) (C : Submodule ℝ (Lp ℝ 2 ν)) : Submodule ℝ (Lp ℝ 2 η) := by
  cases h
  exact C

theorem valueLinear_apply (h : ν=η) (V : D →ₗ[ℝ] Lp ℝ 2 ν) (f : D) :
    valueLinear h V f=vector h (V f) := by cases h; rfl

theorem valueLinear_range (h : ν=η) (V : D →ₗ[ℝ] Lp ℝ 2 ν) :
    LinearMap.range (valueLinear h V)=valueSubmodule h (LinearMap.range V) := by cases h; rfl

theorem pmap_hasCore (h : ν=η) (A : Lp ℝ 2 ν →ₗ.[ℝ] Lp ℝ 2 ν)
    (C : Submodule ℝ (Lp ℝ 2 ν)) (hC : A.HasCore C) :
    (pmap h A).HasCore (valueSubmodule h C) := by cases h; exact hC
end LawTransport

private theorem domRestrict_action {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ.[ℝ] E) (C : Submodule ℝ E) (u v : E)
    (hA : ∃ hd : u∈A.domain, A ⟨u,hd⟩=v) (hC : u∈C) :
    ∃ hd : u∈(A.domRestrict C).domain, (A.domRestrict C) ⟨u,hd⟩=v := by
  obtain ⟨hd,ha⟩ := hA
  exact ⟨⟨hC,hd⟩,ha⟩

def literalC2ValueLinear (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    c2Functions (n+1) →ₗ[ℝ] LiteralGibbsL2 n μ J β :=
  LawTransport.valueLinear (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (c2ValueLinear (by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous)

theorem literalC2ValueLinear_apply (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (f : c2Functions (n+1)) :
    literalC2ValueLinear n μ J hJ β f =
      literalGibbsToL2 n μ J hJ β f (c2Functions_contDiff f).continuous :=
  LawTransport.valueLinear_apply (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (c2ValueLinear (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous) f

theorem literalWeakGenerator_C2_hasCore (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    (literalWeakGenerator n μ J hJ β).HasCore
      (LinearMap.range (literalC2ValueLinear n μ J hJ β)) := by
  have hc := sphericalGenerator_C2_hasCore (show 1≤n+1 by omega) β
    (regularAmbientField n μ J) (regularAmbientField_contDiff n μ J)
  have ht := LawTransport.pmap_hasCore (literal_gibbsLaw_eq_regular n μ β J hJ).symm
    (sphericalGenerator (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous)
    (LinearMap.range (c2ValueLinear (show 1≤n+1 by omega) β (regularAmbientField n μ J)
      (regularAmbientField_contDiff n μ J).continuous)) hc
  rw [← LawTransport.valueLinear_range] at ht
  exact ht

def literalC2DifferentialOperator (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    LiteralGibbsL2 n μ J β →ₗ.[ℝ] LiteralGibbsL2 n μ J β :=
  (literalWeakGenerator n μ J hJ β).domRestrict
    (LinearMap.range (literalC2ValueLinear n μ J hJ β))

theorem literalC2DifferentialOperator_domain (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    (literalC2DifferentialOperator n μ J hJ β).domain =
      LinearMap.range (literalC2ValueLinear n μ J hJ β) :=
  inf_eq_left.mpr (literalWeakGenerator_C2_hasCore n μ J hJ β).le_domain

/-- Every global C² test is in the literal differential domain, and its
action is the negative of the actual spherical Langevin differential expression. -/
theorem literalC2DifferentialOperator_apply (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ hdom : literalGibbsToL2 n μ J hJ β f hf.continuous ∈
        (literalC2DifferentialOperator n μ J hJ β).domain,
      literalC2DifferentialOperator n μ J hJ β
        ⟨literalGibbsToL2 n μ J hJ β f hf.continuous,hdom⟩ =
      (-1 : ℝ) • literalGibbsToL2 n μ J hJ β
        (rotationGenerator (n+1) β (regularAmbientField n μ J) f)
        (rotationGenerator_continuous β ((regularAmbientField_contDiff n μ J).of_le
          (by norm_num)) hf) := by
  have hv : literalGibbsToL2 n μ J hJ β f hf.continuous ∈
      LinearMap.range (literalC2ValueLinear n μ J hJ β) :=
    ⟨⟨f,hf⟩,literalC2ValueLinear_apply n μ J hJ β ⟨f,hf⟩⟩
  exact domRestrict_action (literalWeakGenerator n μ J hJ β)
    (LinearMap.range (literalC2ValueLinear n μ J hJ β)) _ _
    (literalWeakGenerator_C2 n μ J hJ β f hf) hv

theorem literalC2DifferentialOperator_closure (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    (literalC2DifferentialOperator n μ J hJ β).closure = literalWeakGenerator n μ J hJ β :=
  (literalWeakGenerator_C2_hasCore n μ J hJ β).closure_eq

theorem literalC2DifferentialOperator_essentiallySelfAdjoint (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) :
    IsSelfAdjoint (literalC2DifferentialOperator n μ J hJ β).closure := by
  rw [literalC2DifferentialOperator_closure]
  exact literalWeakGenerator_selfAdjoint n μ J hJ β

theorem literal_C2_essentiallySelfAdjoint_ae (n : ℕ) (μ : InfiniteMixture) (β : ℝ) :
    ∀ᵐ J ∂disorderLaw (n+1),∃ hJ : J∈summableJetDisorder μ,
      IsSelfAdjoint (literalC2DifferentialOperator n μ J hJ β).closure := by
  filter_upwards [summableJetDisorder_ae (by omega : 0<n+1) μ] with J hJ
  exact ⟨hJ,literalC2DifferentialOperator_essentiallySelfAdjoint n μ J hJ β⟩

end SlowEquilibration.SphericalInfiniteModel
