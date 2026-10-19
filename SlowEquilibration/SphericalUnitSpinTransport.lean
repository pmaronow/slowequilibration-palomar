-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPerturbationPairMass
public import SlowEquilibration.GaussianGibbsAssociation
public import SlowEquilibration.GaussianGibbsTransport
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! Canonical actual transport between a fixed positive-radius sphere law
and its literal unit-sphere subtype law. The construction uses radial
scaling and subtype comap; no off-sphere choice or replacement measure
is involved. It commutes with genuine normalized Gibbs tilts. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary radial scaling to radius one. -/
def scaleToUnit {N : ℕ} (r : ℝ) (x : Vector N) : Vector N := r⁻¹ • x

/-- The canonical unit-sphere law of a supported ambient spherical law. -/
def unitLaw {N : ℕ} (μ : Measure (Vector N)) (r : ℝ) : Measure (UnitSpin N) :=
  (μ.map (scaleToUnit r)).comap Subtype.val

/-- Literal embedding back to the original radius. -/
def fromUnit {N : ℕ} (r : ℝ) (z : UnitSpin N) : Vector N := r • z.val

theorem scaleToUnit_measurable (N : ℕ) (r : ℝ) : Measurable (scaleToUnit (N := N) r) := by
  unfold scaleToUnit
  fun_prop

theorem fromUnit_measurable (N : ℕ) (r : ℝ) : Measurable (fromUnit (N := N) r) := by
  unfold fromUnit
  fun_prop

theorem unitSpin_measurableSet (N : ℕ) : MeasurableSet {x : Vector N | ‖x‖=1} :=
  (isClosed_eq continuous_norm continuous_const).measurableSet

/-- Exact support of the scaled ambient law. -/
theorem scaleToUnit_support {N : ℕ} (μ : Measure (Vector N)) {r : ℝ} (hr : 0<r)
    (hμ : ∀ᵐ x ∂μ,‖x‖=r) : ∀ᵐ x ∂μ.map (scaleToUnit r), ‖x‖=1 := by
  apply (ae_map_iff (scaleToUnit_measurable N r).aemeasurable (unitSpin_measurableSet N)).mpr
  filter_upwards [hμ] with x hx
  rw [scaleToUnit,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),hx,inv_mul_cancel₀ hr.ne']

/-- The subtype construction retains precisely the actual scaled law. -/
theorem unitLaw_map_val {N : ℕ} (μ : Measure (Vector N)) {r : ℝ} (hr : 0<r)
    (hμ : ∀ᵐ x ∂μ,‖x‖=r) : (unitLaw μ r).map Subtype.val=μ.map (scaleToUnit r) := by
  have he : MeasurableEmbedding (Subtype.val : UnitSpin N → Vector N) :=
    MeasurableEmbedding.subtype_coe (unitSpin_measurableSet N)
  rw [unitLaw,he.map_comap,Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem ((scaleToUnit_support μ hr hμ).mono fun x hx => hx)

/-- A genuine spherical probability law gives a genuine probability law
on the ordinary unit-spin subtype, even when its distribution is singular. -/
theorem unitLaw_probability {N : ℕ} (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0<r) (hμ : ∀ᵐ x ∂μ,‖x‖=r) : IsProbabilityMeasure (unitLaw μ r) := by
  unfold unitLaw
  apply (MeasurableEmbedding.subtype_coe (unitSpin_measurableSet N)).isProbabilityMeasure_comap
  exact (scaleToUnit_support μ hr hμ).mono fun x hx => ⟨⟨x,hx⟩,rfl⟩

/-- Radial transport back is exactly the original ambient spherical law. -/
theorem unitLaw_map_fromUnit {N : ℕ} (μ : Measure (Vector N)) {r : ℝ} (hr : 0<r)
    (hμ : ∀ᵐ x ∂μ,‖x‖=r) : (unitLaw μ r).map (fromUnit r)=μ := by
  calc
    _=((unitLaw μ r).map Subtype.val).map (fun x : Vector N => r • x) := by
      rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
      rfl
    _=(μ.map (scaleToUnit r)).map (fun x : Vector N => r • x) := by rw [unitLaw_map_val μ hr hμ]
    _=μ := by
      rw [Measure.map_map (by fun_prop) (scaleToUnit_measurable N r)]
      have heq : (fun x : Vector N => r • x) ∘ scaleToUnit r=id := by
        funext x
        simp only [Function.comp_def,scaleToUnit,smul_smul,mul_inv_cancel₀ hr.ne',one_smul,id_eq]
      rw [heq,Measure.map_id]

theorem fromUnit_measurableEmbedding (N : ℕ) {r : ℝ} (hr : r≠0) :
    MeasurableEmbedding (fromUnit (N := N) r) :=
  (measurableEmbedding_const_smul₀ hr).comp
    (MeasurableEmbedding.subtype_coe (unitSpin_measurableSet N))

/-- True Gibbs transport from the canonical unit-sphere law. -/
theorem unitLaw_gibbs_map {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure (Vector N)) {r : ℝ} (hr : 0<r) (hμ : ∀ᵐ x ∂μ,‖x‖=r)
    (L : Vector N → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) :
    (gibbsMeasure (unitLaw μ r) (fun z => L (fromUnit r z)) w).map (fromUnit r)=
      gibbsMeasure μ L w := by
  rw [gibbsMeasure_map _ _ (fromUnit_measurable N r) L hL w,unitLaw_map_fromUnit μ hr hμ]

/-- Extracting the canonical unit law commutes with the actual Gibbs
normalization. This identifies conditioned spherical banks with the
ordinary unit-spin Gibbs base laws used by uniform positivity. -/
theorem unitLaw_gibbsMeasure {N : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure (Vector N))
    {r : ℝ} (hr : 0<r) (hμ : ∀ᵐ x ∂μ,‖x‖=r)
    (L : Vector N → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) :
    unitLaw (gibbsMeasure μ L w) r=
      gibbsMeasure (unitLaw μ r) (fun z => L (fromUnit r z)) w := by
  have hac : gibbsMeasure μ L w≪μ := withDensity_absolutelyContinuous _ _
  have hG : ∀ᵐ x ∂gibbsMeasure μ L w,‖x‖=r := hac.ae_le hμ
  apply (fromUnit_measurableEmbedding N hr.ne').map_injective
  rw [unitLaw_map_fromUnit _ hr hG,unitLaw_gibbs_map μ hr hμ L hL w]

/-- Actual manuscript-radius support suffices, without a supplied radial
or unit law. -/
theorem norm_eq_sqrt_of_norm_sq {N : ℕ} (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) :
    ‖x‖=Real.sqrt N := by
  nlinarith [norm_nonneg x,Real.sqrt_nonneg (N:ℝ),Real.sq_sqrt (Nat.cast_nonneg N)]

end SlowEquilibration.SphericalPositivePerturbation
