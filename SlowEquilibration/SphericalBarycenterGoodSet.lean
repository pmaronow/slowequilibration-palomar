module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterConstruction
public import SlowEquilibration.SphericalGoodCapCoreCollar

@[expose] public section

/-! # Constructed barycenter on the actual good-reference event

The good set is the Borel set defined by the literal restricted-partition
tests. Its core mass supplies the high cap mass, and the constructed smooth
observable then satisfies the source energy and alignment estimates. This
module exposes the remaining pressure and joint-test failure probabilities
without assuming a good Gibbs set or an aligned low-energy observable.
-/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace
variable {N P : ℕ}

/-- The literal good-reference set determined by the source partition tests. -/
def sourceGoodSet (c : Degree P → ℝ) (β F J G δ q₁ q₂ q w : ℝ)
    (D : Disorder N P) : Set (Vector N) :=
  goodReferenceSet (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w) D

lemma sourceGoodSet_measurable (c : Degree P → ℝ) (β F J G δ q₁ q₂ q w : ℝ)
    (D : Disorder N P) : MeasurableSet (sourceGoodSet c β F J G δ q₁ q₂ q w D) :=
  goodReferenceSet_measurable (capCoreCollarBadEvent_measurable c β F J G δ q₁ q₂ q w) D

lemma sourceGoodSet_onSphere (c : Degree P → ℝ) (β F J G δ q₁ q₂ q w : ℝ)
    (D : Disorder N P) {x : Vector N} (hx : x ∈ sourceGoodSet c β F J G δ q₁ q₂ q w D) :
    OnSphere x :=
  (onSphere_iff_norm_sq x).mpr (goodReferenceSet_subset_sphere _ D hx)

lemma collar_eq_model_collar (x : Vector N) (q₁ q₂ : ℝ) :
    collar x q₁ q₂ = SphericalModel.collar x q₁ q₂ := by
  ext u
  simp only [collar,SphericalModel.collar,mem_ofPred_eq,overlap,real_inner_comm]

lemma coreBand_subset_cap (x : Vector N) (q w q₂ : ℝ) (hcore : q₂ ≤ q-w) :
    coreBand x q w ⊆ cap x q₂ := by
  intro u hu
  change |overlap u x-q| ≤ w at hu
  have hl := (abs_le.mp hu).1
  change q₂ ≤ overlap u x
  linarith

/-- The actual partition-test event produces the two literal mass inputs
needed by the barycenter, including the source core-to-high-cap inclusion. -/
theorem sourceGoodSet_cap_collar_of_event (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β F J G δ q₁ q₂ q w r : ℝ) (hcore : q₂ ≤ q-w) (D : Disorder N P)
    (hD : D ∈ goodCapCoreCollarEvent c β F J G δ q₁ q₂ q w r) :
    (gibbsLaw N β (field c D)).real (sourceGoodSet c β F J G δ q₁ q₂ q w D)ᶜ ≤ r ∧
      ∀ x ∈ sourceGoodSet c β F J G δ q₁ q₂ q w D,
        Real.exp (-(J+2*δ)*(N:ℝ)) ≤ (gibbsLaw N β (field c D)).real (cap x q₂) ∧
        (gibbsLaw N β (field c D)).real (collar x q₁ q₂) ≤
          Real.exp (-(J+G-2*δ)*(N:ℝ)) := by
  let := gibbsLaw_probability hN β (field_contDiff c D).continuous
  refine ⟨hD.2,?_⟩
  intro x hx
  obtain ⟨_,hband,hcollar⟩ := goodReferenceSet_cap_core_collar hN c β F J G δ q₁ q₂ q w D hD.1 hx
  have hcap := hband.trans (measureReal_mono (coreBand_subset_cap x q w q₂ hcore))
  rw [← collar_eq_model_collar] at hcollar
  constructor
  · convert hcap using 1 <;> congr 1 <;> ring
  · convert hcollar using 1 <;> congr 1 <;> ring

/-- The literal good-reference event yields a Borel spherical good set and
the actual constructed observable with uniform energy and alignment rates.
Constants are fixed before every dimension, mixture, disorder and field. -/
theorem sourceObservable_on_goodReference_event_eventually (J G δ q₁ q₂ a q₀ : ℝ)
    (hJ : 0 < J) (hδ : 0 ≤ δ) (hgap : 4*δ < G) (ha : 0 < a)
    (hq₁ : 0 < q₁) (hq : q₁ < q₂) (hq₀ : q₀ < q₁) :
    ∃ C cE : ℝ, 0 < C ∧ 0 < cE ∧ cE=min (G-4*δ) a/2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (P : ℕ) (c : Degree P → ℝ) (β F q w : ℝ)
        (D : Disorder N P), q₂ ≤ q-w →
        D ∈ goodCapCoreCollarEvent c β F J G δ q₁ q₂ q w (Real.exp (-a*(N:ℝ))) →
        MeasurableSet (sourceGoodSet c β F J G δ q₁ q₂ q w D) ∧
        (∀ x ∈ sourceGoodSet c β F J G δ q₁ q₂ q w D, OnSphere x) ∧
        (gibbsLaw N β (field c D)).real (sourceGoodSet c β F J G δ q₁ q₂ q w D)ᶜ ≤
          Real.exp (-a*(N:ℝ)) ∧
        ContDiff ℝ ∞ (sourceObservable β (field c D) J δ q₁ q₂) ∧
        (∀ x, ‖sourceObservable β (field c D) J δ q₁ q₂ x‖ ≤ 1) ∧
        vectorDirichletEnergy β (field c D) (sourceObservable β (field c D) J δ q₁ q₂) ≤
          C*Real.exp (-cE*(N:ℝ)) ∧
        (∀ x ∈ sourceGoodSet c β F J G δ q₁ q₂ q w D,
          q₀ ≤ inner ℝ (spin x) (sourceObservable β (field c D) J δ q₁ q₂ x) ∧
          3*q₁/4 ≤ inner ℝ (spin x) (sourceObservable β (field c D) J δ q₁ q₂ x)) ∧
        q₁-(1+q₁)*(Real.exp (-(N:ℝ))+Real.exp (-a*(N:ℝ))) ≤
          ∫ x, inner ℝ (spin x) (sourceObservable β (field c D) J δ q₁ q₂ x)
            ∂gibbsLaw N β (field c D) := by
  obtain ⟨M,C,cE,_,hC,hcE,hcEq,_,he⟩ :=
    sourceObservable_estimates_eventually J G δ q₁ q₂ a q₀ hJ hδ hgap ha hq₁ hq hq₀
  refine ⟨C,cE,hC,hcE,hcEq,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),he] with N hN hE
  intro P c β F q w D hcore hD
  have hS := sourceGoodSet_measurable c β F J G δ q₁ q₂ q w D
  obtain ⟨hbad,hmass⟩ := sourceGoodSet_cap_collar_of_event hN c β F J G δ q₁ q₂ q w
    (Real.exp (-a*(N:ℝ))) hcore D hD
  obtain ⟨hsm,hnorm,henergy,halign,hmean⟩ := hE β (field c D) (field_contDiff c D).continuous
    (sourceGoodSet c β F J G δ q₁ q₂ q w D) hS hbad
    (fun x hx _ => (hmass x hx).1) (fun x hx _ => (hmass x hx).2)
  refine ⟨hS,fun x hx => sourceGoodSet_onSphere c β F J G δ q₁ q₂ q w D hx,
    hbad,hsm,hnorm,henergy,?_,hmean⟩
  intro x hx
  exact halign x hx (sourceGoodSet_onSphere c β F J G δ q₁ q₂ q w D hx)

/-- Failure of the actual good-reference event is controlled by the actual
pressure failure and joint partition-test mass. These two probabilities
remain visible quantitative obligations rather than hidden premises. -/
theorem source_good_event_failure_le (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β F J G δ q₁ q₂ q w a : ℝ) :
    (disorderLaw N P).real
      (goodCapCoreCollarEvent c β F J G δ q₁ q₂ q w (Real.exp (-a*(N:ℝ))))ᶜ ≤
      (disorderLaw N P).real {D | δ < |Real.log (partition N β (field c D))/(N:ℝ)-F|}+
        (gibbsReferenceLaw (N := N) c β).real
          (capCoreCollarBadEvent c β F J G δ q₁ q₂ q w)*Real.exp (a*(N:ℝ)) := by
  have h := goodCapCoreCollarEvent_failure_le hN c β F J G δ q₁ q₂ q w
    (Real.exp_pos (-a*(N:ℝ)))
  convert h using 1
  rw [div_eq_mul_inv,← Real.exp_neg]
  congr 3
  ring

end
end SlowEquilibration.SphericalBarycenter
