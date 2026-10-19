-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.OrderedTensorTraceGaussianBank
public import SlowEquilibration.PureTensorJetBounds

/-! Uniform physical bounds for actual fixed-slot traces of the original
ordered tensor. The normalized trace bank has its proved original iid law,
and the true Hamiltonian normalization gives the source N^(1-j/2) scale. -/

@[expose] public section
namespace SlowEquilibration.OrderedTensorTraceGaussianBank
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalAging.FiniteModel SphericalAging.LandscapeDerivatives
open PureTensorJetFeatures PureTensorJetBounds
open scoped RealInnerProductSpace BigOperators
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rawOrderedTensorTrace (N q j : ℕ) (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) :
    SphericalAging.FiniteModel.Disorder N q := fun a => orderedTensorTrace N q j J a

/-- Exact original product law of every normalized trace coefficient. -/
theorem actual_rawOrderedTensorTrace_hasLaw {N : ℕ} (hN : 0 < N) (q j : ℕ) :
    HasLaw (rawOrderedTensorTrace N q j) (SphericalAging.FiniteModel.disorderLaw N q)
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) := by
  have hdecodeM : Measurable (fun z : EuclideanSpace ℝ (TensorIndex N q) => fun a => z a) := by
    fun_prop
  have hflattenM : Measurable (tensorFlatten (N := N) (p := q)) :=
    (PiLp.continuous_toLp 2 _).measurable
  have hflat : (SphericalAging.FiniteModel.disorderLaw N q).map tensorFlatten=
      stdGaussian (EuclideanSpace ℝ (TensorIndex N q)) := map_pi_eq_stdGaussian
  have hdecode : HasLaw (fun z : EuclideanSpace ℝ (TensorIndex N q) => fun a => z a)
      (SphericalAging.FiniteModel.disorderLaw N q)
      (stdGaussian (EuclideanSpace ℝ (TensorIndex N q))) := by
    refine ⟨hdecodeM.aemeasurable,?_⟩
    rw [←hflat,Measure.map_map hdecodeM hflattenM]
    change (SphericalAging.FiniteModel.disorderLaw N q).map id=_
    rw [Measure.map_id]
  exact hdecode.fun_comp (actual_orderedTensorTrace_hasLaw hN q j)

def tracedUnitEnvelope (N q j : ℕ) (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) : ℝ :=
  unitJetEnvelope N q 0 (rawOrderedTensorTrace N q j J)

theorem tracedUnitEnvelope_integrable {N : ℕ} (hN : 0 < N) (q j : ℕ) :
    Integrable (tracedUnitEnvelope N q j) (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) :=
  (actual_rawOrderedTensorTrace_hasLaw hN q j).integrable_comp (unitJetEnvelope_integrable hN)

/-- The genuine normalized trace-bank supremum has the correct sqrt(N)
bound, obtained from its actual iid tensor law. -/
theorem expected_tracedUnitEnvelope_le {N q : ℕ} (hN : 0 < N) (hq : 1 ≤ q) (j : ℕ) :
    (∫ J,tracedUnitEnvelope N q j J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j)) ≤
      4*Real.sqrt q*Real.sqrt N := by
  have h := (actual_rawOrderedTensorTrace_hasLaw hN q j).integral_comp
    (unitJetEnvelope_integrable (N := N) (p := q) (j := 0) hN).aestronglyMeasurable
  change (∫ J,tracedUnitEnvelope N q j J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j))=
    ∫ J,unitJetEnvelope N q 0 J ∂SphericalAging.FiniteModel.disorderLaw N q at h
  rw [h]
  have hb := expected_unitJetEnvelope_le (N := N) (p := q) (j := 0) hN hq
  norm_num at hb
  exact hb

/-- The degree-zero trace bank retains its genuine independent constant
Gaussian coefficient; its envelope has dimension-independent expectation. -/
theorem expected_tracedUnitEnvelope_zero_le_one {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (∫ J,tracedUnitEnvelope N 0 j J ∂SphericalAging.FiniteModel.disorderLaw N (0+j+j)) ≤ 1 := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hb (J : SphericalAging.FiniteModel.Disorder N 0) :
      unitJetEnvelope N 0 0 J ≤ ‖tensorFlatten J‖ := by
    change (⨆ v : Bool × UnitBlocks N 0,
      inner ℝ (signedFeature (unitInsertion N 0 0) v) (tensorFlatten J)) ≤ _
    apply ciSup_le
    intro v
    have hn : ‖unitInsertion N 0 0 v.2‖ ≤ 1 := by
      simpa only [unitInsertion,pow_zero] using insertionFeature_norm_le (p := 0)
        (fun k => (v.2 k).val) (fun k => unit_norm (v.2 k))
    have hs : ‖signedFeature (unitInsertion N 0 0) v‖ ≤ 1 := by
      simpa only [signedFeature,norm_smul,Real.norm_eq_abs,abs_sign,one_mul] using hn
    exact (real_inner_le_norm _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (norm_nonneg (tensorFlatten J)))
  have hflat : HasLaw (tensorFlatten (N := N) (p := 0))
      (stdGaussian (EuclideanSpace ℝ (TensorIndex N 0)))
      (SphericalAging.FiniteModel.disorderLaw N 0) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have hgn := GaussianNormMean.integral_norm_stdGaussian_le_sqrt_finrank
    (E := EuclideanSpace ℝ (TensorIndex N 0))
  have hi := hflat.integral_comp IsGaussian.integrable_id.norm.aestronglyMeasurable
  have hraw := integral_mono (unitJetEnvelope_integrable (p := 0) (j := 0) hN)
    (hflat.integrable_comp IsGaussian.integrable_id.norm) hb
  rw [hi] at hraw
  have hdecode := (actual_rawOrderedTensorTrace_hasLaw hN 0 j).integral_comp
    (unitJetEnvelope_integrable (p := 0) (j := 0) hN).aestronglyMeasurable
  change (∫ J,tracedUnitEnvelope N 0 j J ∂SphericalAging.FiniteModel.disorderLaw N (0+j+j))=_ at hdecode
  rw [hdecode]
  exact hraw.trans (by simpa only [finrank_euclideanSpace,Fintype.card_fun,
    Fintype.card_fin,pow_zero,Nat.cast_one,Real.sqrt_one,id_eq] using hgn)

/-- One formula covers the positive-degree and constant trace banks. -/
theorem expected_tracedUnitEnvelope_le_all {N : ℕ} (hN : 0 < N) (q j : ℕ) :
    (∫ J,tracedUnitEnvelope N q j J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j)) ≤
      4*Real.sqrt (q+1)*Real.sqrt N := by
  by_cases hq : q=0
  · subst q
    apply (expected_tracedUnitEnvelope_zero_le_one hN j).trans
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs : 1 ≤ Real.sqrt N := by rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)]; simpa
    norm_num
    nlinarith
  · apply (expected_tracedUnitEnvelope_le hN (by omega : 1 ≤ q) j).trans
    gcongr
    exact_mod_cast Nat.le_add_right q 1

/-- Literal j-fold fixed-slot trace of the original physical Hamiltonian. -/
def tracedHamiltonian (N q j : ℕ) (J : SphericalAging.FiniteModel.Disorder N (q+j+j))
    (x : Vector N) : ℝ :=
  normalization N (q+j+j)*∑ a : TensorIndex N q,
    (∑ b : TensorIndex N j,J (tracedIndex a b))*∏ k : Fin q,x (a k)

theorem tracedHamiltonian_eq_actual_bank {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (x : Vector N) :
    tracedHamiltonian N q j J x=
      (normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)/normalization N q)*
        Hamiltonian N q (rawOrderedTensorTrace N q j J) x := by
  have hnorm : normalization N q≠0 := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).ne'
  have hs : Real.sqrt ((N : ℝ)^j)≠0 :=
    (Real.sqrt_pos.mpr (pow_pos (Nat.cast_pos.mpr hN) j)).ne'
  have hraw (a : TensorIndex N q) : (∑ b : TensorIndex N j,J (tracedIndex a b))=
      Real.sqrt ((N : ℝ)^j)*rawOrderedTensorTrace N q j J a := by
    rw [rawOrderedTensorTrace,orderedTensorTrace_apply]
    field_simp [hs]
  unfold tracedHamiltonian Hamiltonian tensorMonomial
  simp_rw [hraw,mul_assoc]
  rw [←Finset.mul_sum]
  field_simp [hnorm]

def tracedPhysicalEnvelope (N q j : ℕ) (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) : ℝ :=
  normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q*tracedUnitEnvelope N q j J

/-- Every actual physical trace evaluation is bounded by this envelope,
uniformly throughout the true radius-sqrt(N) ball. -/
theorem tracedHamiltonian_abs_le_envelope {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (x : Vector N)
    (hx : ‖x‖ ≤ Real.sqrt N) : |tracedHamiltonian N q j J x| ≤ tracedPhysicalEnvelope N q j J := by
  have hnorm : normalization N q≠0 := (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).ne'
  have hscale : 0 ≤ normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)/normalization N q := by
    apply div_nonneg
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.sqrt_nonneg _)
    · exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hH := iteratedFDeriv_norm_le_pureJetEnvelope (j := 0) hN (rawOrderedTensorTrace N q j J) x hx
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hH
  rw [tracedHamiltonian_eq_actual_bank hN q j J x,abs_mul,abs_of_nonneg hscale]
  apply (mul_le_mul_of_nonneg_left hH hscale).trans_eq
  unfold pureJetEnvelope tracedPhysicalEnvelope tracedUnitEnvelope
  simp only [Nat.sub_zero]
  field_simp [hnorm]

theorem tracedPhysicalEnvelope_integrable {N : ℕ} (hN : 0 < N) (q j : ℕ) :
    Integrable (tracedPhysicalEnvelope N q j)
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) :=
  (tracedUnitEnvelope_integrable hN q j).const_mul _

theorem sqrt_dimension_pow (N j : ℕ) : Real.sqrt ((N : ℝ)^j)=(Real.sqrt N)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg N) j),ih,pow_succ]

/-- Exact physical dimensional normalization of the literal fixed-slot
trace, with no asymptotic coefficient assumption. -/
theorem trace_physical_normalization {N q : ℕ} (hN : 0 < N) (hq : 1 ≤ q) (j : ℕ) :
    normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q*Real.sqrt N=
      (N : ℝ)^(1-(j : ℝ)/2) := by
  rw [sqrt_dimension_pow]
  have hp : 1 ≤ q+j+j := by omega
  have hj : j ≤ q+j+j := by omega
  have hpow : q+j+j-j=q+j := by omega
  calc
    _=normalization N (q+j+j)*(Real.sqrt N)^(q+j)*Real.sqrt N := by rw [pow_add];ring
    _=(N : ℝ)^(1-(j : ℝ)/2) := by
      simpa only [hpow] using physical_normalization_identity hN hp hj

/-- The same exact normalization also includes a constant traced field,
provided the original ordered tensor has positive degree. -/
theorem trace_physical_normalization_of_degree {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (hp : 1 ≤ q+j+j) :
    normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q*Real.sqrt N=
      (N : ℝ)^(1-(j : ℝ)/2) := by
  rw [sqrt_dimension_pow]
  have hj : j ≤ q+j+j := by omega
  have hpow : q+j+j-j=q+j := by omega
  calc
    _=normalization N (q+j+j)*(Real.sqrt N)^(q+j)*Real.sqrt N := by rw [pow_add];ring
    _=(N : ℝ)^(1-(j : ℝ)/2) := by
      simpa only [hpow] using physical_normalization_identity hN hp hj

/-- Actual original-tensor expected trace supremum at the manuscript
N^(1-j/2) scale, proved from the concrete trace Gaussian bank. -/
theorem expected_tracedPhysicalEnvelope_le {N q : ℕ} (hN : 0 < N) (hq : 1 ≤ q) (j : ℕ) :
    (∫ J,tracedPhysicalEnvelope N q j J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j)) ≤
      4*Real.sqrt q*(N : ℝ)^(1-(j : ℝ)/2) := by
  unfold tracedPhysicalEnvelope
  rw [integral_const_mul]
  have hs : 0 ≤ normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.sqrt_nonneg _)) (pow_nonneg (Real.sqrt_nonneg _) _)
  have h := mul_le_mul_of_nonneg_left (expected_tracedUnitEnvelope_le hN hq j) hs
  apply h.trans_eq
  calc
    _=4*Real.sqrt q*(normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q*Real.sqrt N) := by ring
    _=_ := by rw [trace_physical_normalization hN hq j]

/-- Uniform source-scale expected envelope including fully traced even tensors. -/
theorem expected_tracedPhysicalEnvelope_le_all {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (hp : 1 ≤ q+j+j) :
    (∫ J,tracedPhysicalEnvelope N q j J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j)) ≤
      4*Real.sqrt (q+1)*(N : ℝ)^(1-(j : ℝ)/2) := by
  unfold tracedPhysicalEnvelope
  rw [integral_const_mul]
  have hs : 0 ≤ normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (Real.sqrt_nonneg _)) (pow_nonneg (Real.sqrt_nonneg _) _)
  have h := mul_le_mul_of_nonneg_left (expected_tracedUnitEnvelope_le_all hN q j) hs
  apply h.trans_eq
  calc
    _=4*Real.sqrt (q+1)*(normalization N (q+j+j)*Real.sqrt ((N : ℝ)^j)*(Real.sqrt N)^q*Real.sqrt N) := by ring
    _=_ := by rw [trace_physical_normalization_of_degree hN q j hp]

end
end SlowEquilibration.OrderedTensorTraceGaussianBank
