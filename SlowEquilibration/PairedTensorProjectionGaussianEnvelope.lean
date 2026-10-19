-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairedTensorProjectionMetric
public import SlowEquilibration.OrderedTensorTracePhysicalEnvelope
public import SlowEquilibration.ConstrainedConcentration

/-! Actual original ordered-tensor all-order projected Gaussian envelopes.
Model orders are fixed before N. Expectation and exponential tails come
from coefficient features and Gaussian comparison/concentration. -/

@[expose] public section
namespace SlowEquilibration.PairedTensorProjectionFeatures
noncomputable section
open MeasureTheory ProbabilityTheory SphericalAging.FiniteModel SphericalProjectionMatrixFeature
open PureTensorJetBounds GaussianCompactMaximum GaussianSharpAbsoluteMaximum
open OrderedTensorTraceGaussianBank
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pairedPhysicalScale (N q j : ℕ) : ℝ :=
  normalization N (q+j+j)/Real.sqrt N*((Real.sqrt N)^q*(Real.sqrt ((N : ℝ)-1))^j)

theorem pairedPhysicalScale_nonneg (N q j : ℕ) : 0≤pairedPhysicalScale N q j := by
  unfold pairedPhysicalScale normalization
  positivity

/-- The genuine projected scale is no greater than the original trace scale. -/
theorem pairedPhysicalScale_sqrt_dimension_le {N : ℕ} (hN : 2≤N) (q j : ℕ)
    (hp : 1≤q+j+j) :
    pairedPhysicalScale N q j*Real.sqrt N ≤ (N : ℝ)^((1-(j : ℝ))/2) := by
  have hNr : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hs : Real.sqrt (N : ℝ)≠0 := (Real.sqrt_pos.mpr hNr).ne'
  have he : normalization N (q+j+j)*(Real.sqrt N)^q*(Real.sqrt N)^j=
      (N : ℝ)^((1-(j : ℝ))/2) := by
    have h := trace_physical_normalization_of_degree (N := N) (by omega) q j hp
    rw [sqrt_dimension_pow] at h
    have hc : (N : ℝ)^((1-(j : ℝ))/2)*Real.sqrt N=(N : ℝ)^(1-(j : ℝ)/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add hNr]
      congr 1
      ring
    apply (mul_right_cancel₀ hs)
    calc
      _=normalization N (q+j+j)*(Real.sqrt N)^j*(Real.sqrt N)^q*Real.sqrt N := by ring
      _=(N : ℝ)^(1-(j : ℝ)/2) := h
      _=_ := hc.symm
  calc
    _=normalization N (q+j+j)*(Real.sqrt N)^q*(Real.sqrt ((N : ℝ)-1))^j := by
      unfold pairedPhysicalScale
      field_simp
    _≤normalization N (q+j+j)*(Real.sqrt N)^q*(Real.sqrt N)^j := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) j)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (pow_nonneg (Real.sqrt_nonneg _) q))
    _=_ := he

/-- Every higher paired order has coefficient Lipschitz scale at most N^(-1/2). -/
theorem pairedPhysicalScale_le_inv_sqrt {N : ℕ} (hN : 2≤N) (q j : ℕ) (hj : 0<j) :
    pairedPhysicalScale N q j≤(Real.sqrt N)⁻¹ := by
  have hNr : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hjr : (1 : ℝ)≤j := by exact_mod_cast hj
  have h := (pairedPhysicalScale_sqrt_dimension_le hN q j (by omega)).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith))
  rw [←one_div]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (show 0<N by omega)))).mpr h

def pairedGaussianFeature (N q j : ℕ) (u : UnitSphere N) :
    EuclideanSpace ℝ (TensorIndex N (q+j+j)) :=
  pairedPhysicalScale N q j • unitPairedFeature N q j u

def pairedGaussianEnvelope (N q j : ℕ) (g : EuclideanSpace ℝ (TensorIndex N (q+j+j))) : ℝ :=
  absoluteSupremum (pairedGaussianFeature N q j) g

theorem pairedGaussianFeature_continuous (N q j : ℕ) : Continuous (pairedGaussianFeature N q j) :=
  (unitPairedFeature_continuous N q j).const_smul (pairedPhysicalScale N q j)

theorem pairedGaussianEnvelope_integrable {N : ℕ} (hN : 2≤N) (q j : ℕ) :
    Integrable (pairedGaussianEnvelope N q j)
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j))) := by
  let : NeZero N := ⟨by omega⟩
  exact absoluteSupremum_integrable _ (pairedGaussianFeature_continuous N q j)

/-- Genuine expected original Gaussian projected trace bound, including q=0. -/
theorem expected_pairedGaussianEnvelope_le_dimension_scale {N : ℕ} (hN : 2≤N) (q j : ℕ) (hj : 0<j) :
    (∫ g,pairedGaussianEnvelope N q j g
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j))) ≤
      2*Real.sqrt ((q : ℝ)+4*j)*(N : ℝ)^((1-(j : ℝ))/2) := by
  let : NeZero N := ⟨by omega⟩
  have hC : 1≤Real.sqrt ((q : ℝ)+4*j) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    have hjr : (1 : ℝ)≤j := by exact_mod_cast hj
    nlinarith [show (0 : ℝ)≤q by positivity]
  have hc := expected_absoluteSupremum_le_twice
    (pairedGaussianFeature N q j) (fun u : UnitSphere N => (u : Vector N))
    (pairedGaussianFeature_continuous N q j) continuous_subtype_val
    (L := pairedPhysicalScale N q j*Real.sqrt ((q : ℝ)+4*j))
    (mul_nonneg (pairedPhysicalScale_nonneg N q j) (Real.sqrt_nonneg _))
    (fun u => by
      simp only [pairedGaussianFeature,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (pairedPhysicalScale_nonneg N q j),unitPairedFeature_norm hN,mul_one]
      exact le_mul_of_one_le_right (pairedPhysicalScale_nonneg N q j) hC)
    unit_norm
    (fun u v => by
      simp only [pairedGaussianFeature,←smul_sub,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (pairedPhysicalScale_nonneg N q j)]
      exact (mul_le_mul_of_nonneg_left (unitPairedFeature_increment_le hN q j u v)
        (pairedPhysicalScale_nonneg N q j)).trans_eq (by ring))
  have hscale := pairedPhysicalScale_sqrt_dimension_le hN q j (by omega)
  change (∫ g,pairedGaussianEnvelope N q j g ∂_)≤_ at hc
  simp only [Fintype.card_fin] at hc
  have hb := mul_le_mul_of_nonneg_left hscale (show 0≤2*Real.sqrt ((q : ℝ)+4*j) by positivity)
  apply hc.trans
  nlinarith

/-- Every higher paired order has a dimension-independent expected envelope. -/
theorem expected_pairedGaussianEnvelope_le {N : ℕ} (hN : 2≤N) (q j : ℕ) (hj : 0<j) :
    (∫ g,pairedGaussianEnvelope N q j g
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j))) ≤
      2*Real.sqrt ((q : ℝ)+4*j) := by
  have hjr : (1 : ℝ)≤j := by exact_mod_cast hj
  apply (expected_pairedGaussianEnvelope_le_dimension_scale hN q j hj).trans
  have h := Real.rpow_le_one_of_one_le_of_nonpos
    (show (1 : ℝ)≤N by exact_mod_cast (show 1≤N by omega))
    (show (1-(j : ℝ))/2≤0 by linarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h
    (show 0≤2*Real.sqrt ((q : ℝ)+4*j) by positivity)

/-- Coefficient concentration uses the true supremum Lipschitz norm, not a tail premise. -/
theorem pairedGaussianEnvelope_lipschitz {N : ℕ} (hN : 2≤N) (q j : ℕ) (hj : 0<j) :
    LipschitzWith ((Real.sqrt N)⁻¹).toNNReal (pairedGaussianEnvelope N q j) := by
  let : NeZero N := ⟨by omega⟩
  apply field_supremum_lipschitz (fun u : Bool × UnitSphere N =>
    innerSL ℝ (signedFeature (pairedGaussianFeature N q j) u))
  intro u
  simp only [innerSL_apply_norm,signedFeature,norm_smul,Real.norm_eq_abs,abs_sign,one_mul,
    pairedGaussianFeature,abs_of_nonneg (pairedPhysicalScale_nonneg N q j),
    unitPairedFeature_norm hN,mul_one]
  exact pairedPhysicalScale_le_inv_sqrt hN q j hj

/-- Original coefficient Gaussian law has an exponentially small uniform
projected-trace failure probability, for every fixed order. -/
theorem pairedGaussianEnvelope_upper_tail {N : ℕ} (hN : 2≤N) (q j : ℕ) (hj : 0<j)
    {s : ℝ} (hs : 0≤s) :
    SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j))
      {g | 2*Real.sqrt ((q : ℝ)+4*j)+s≤pairedGaussianEnvelope N q j g} ≤
      ENNReal.ofReal (2*Real.exp (-s^2*(N : ℝ)/2)) := by
  have hNr : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega)
  have h := SphericalModel.euclidean_lipschitz_gaussian_closed_tail
    (pairedGaussianEnvelope N q j) (Real.sqrt N)⁻¹ s (inv_pos.mpr (Real.sqrt_pos.mpr hNr)) hs
    (pairedGaussianEnvelope_lipschitz hN q j hj)
  have hsub : {g | 2*Real.sqrt ((q : ℝ)+4*j)+s≤pairedGaussianEnvelope N q j g} ⊆
      {g | s≤|pairedGaussianEnvelope N q j g-(∫ z,pairedGaussianEnvelope N q j z
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j)))|} := by
    intro g hg
    change 2*Real.sqrt ((q : ℝ)+4*j)+s≤pairedGaussianEnvelope N q j g at hg
    have hm := expected_pairedGaussianEnvelope_le hN q j hj
    exact (by linarith : s≤pairedGaussianEnvelope N q j g-(∫ z,pairedGaussianEnvelope N q j z ∂_)).trans (le_abs_self _)
  apply (measure_mono hsub).trans
  convert h using 2
  congr 2
  rw [inv_pow,Real.sq_sqrt hNr.le]
  field_simp

end
end SlowEquilibration.PairedTensorProjectionFeatures
