module
public import FourPapersCommon.ScalarVectorColeHopf
public import QuantitativePaper.BoundedPositiveJets

@[expose] public section

/-! Genuine global smoothness prerequisites for repeated scalar Gaussian
smoothing. All slice regularity follows from bounded positive-order jets, and
all smoothed jet bounds follow from differentiation of actual Gaussian integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper ColeHopfFoundation.ProbabilityTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

theorem exists_lipschitz_of_boundedPositiveJets {f : E → ℝ} (hf : BoundedPositiveJets f) :
    ∃ L : ℝ≥0,LipschitzWith L f := by
  obtain ⟨B,hB,hBound⟩ := hf.2 1 (le_refl 1)
  refine ⟨⟨B,hB⟩,lipschitzWith_of_nnnorm_fderiv_le
    (hf.1.differentiable (by simp)) (fun x=>?_ )⟩
  apply NNReal.coe_le_coe.mp
  convert! hBound x using 1 <;> simp only [norm_iteratedFDeriv_one,NNReal.coe_mk,coe_nnnorm]

theorem boundedPositiveJets_translate {f : E → ℝ} (hf : BoundedPositiveJets f) (x : E) :
    BoundedPositiveJets (fun y=>f (x+y)) := by
  refine ⟨hf.1.comp (contDiff_const.add contDiff_id),?_⟩
  intro j hj
  obtain ⟨B,hB,hBound⟩ := hf.2 j hj
  refine ⟨B,hB,fun y=>?_⟩
  rw [iteratedFDeriv_comp_add_left]
  exact hBound (x+y)

theorem signedScalarDatum_of_boundedPositiveJets {f : ℝ → ℝ}
    (hf : BoundedPositiveJets f) : SignedScalarDatum f := by
  obtain ⟨L,hL⟩ := exists_lipschitz_of_boundedPositiveJets hf
  obtain ⟨B,hB,hBound⟩ := hf.2 2 (by norm_num)
  refine ⟨hf.1.of_le (by simp),⟨L,hL⟩,B,fun x=>?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs] using hBound x

theorem signedScalarDatum_line {f : E → ℝ} (hf : BoundedPositiveJets f) (x v : E) :
    SignedScalarDatum (fun y : ℝ=>f (x+y • v)) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hh := (boundedPositiveJets_translate hf x).comp_linear L
  exact signedScalarDatum_of_boundedPositiveJets hh

theorem boundedPositiveJets_gaussianShiftColeHopf {f : E → ℝ}
    (hf : BoundedPositiveJets f) {n : ℕ} (A : Field n →L[ℝ] E) (m : ℝ) :
    BoundedPositiveJets (gaussianShiftColeHopf A m f) := by
  obtain ⟨L,hL⟩ := exists_lipschitz_of_boundedPositiveJets hf
  have hfinite (N : ℕ) : ∃ K : ℝ,1 ≤ K ∧ ∀ j,1 ≤ j → j ≤ N → ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤ K^j := by
    choose B hB hBound using fun j : {j : ℕ // 1 ≤ j}=>hf.2 j.val j.property
    let C := fun j : ℕ=>if hj : 1 ≤ j then B ⟨j,hj⟩ else 0
    refine ⟨finiteJetPowerBound C N,finiteJetPowerBound_ge_one C N,?_⟩
    intro j hj0 hj x
    apply (hBound ⟨j,hj0⟩ x).trans
    have hh := finite_jet_bound_le_power C N j hj0 hj
    simpa only [C,dif_pos hj0] using hh
  have hout (N : ℕ) : ContDiff ℝ N (gaussianShiftColeHopf A m f) ∧
      ∃ D : ℝ,1 ≤ D ∧ ∀ j,1 ≤ j → j ≤ N → ∀ x,
        ‖iteratedFDeriv ℝ j (gaussianShiftColeHopf A m f) x‖ ≤ D^j := by
    obtain ⟨K,hK,hBound⟩ := hfinite N
    exact gaussianShiftColeHopf_smooth_bounded_jets N f (hf.1.of_le (by simp)) L hL K hK hBound A m
  refine ⟨contDiff_infty.mpr (fun N=>(hout N).1),?_⟩
  intro j hj
  obtain ⟨D,hD,hBound⟩ := (hout j).2
  exact ⟨D^j,pow_nonneg (zero_le_one.trans hD) j,hBound j hj (le_refl j)⟩

theorem boundedPositiveJets_scalarColeHopf {f : E → ℝ} (hf : BoundedPositiveJets f)
    (v : E) (m : ℝ) :
    BoundedPositiveJets (fun x=>coleHopf m 1 (fun y=>f (x+y • v)) 0) := by
  have he : (fun x=>coleHopf m 1 (fun y=>f (x+y • v)) 0)=
      gaussianShiftColeHopf (scalarGaussianShift v) m f :=
    funext (fun x=>coleHopf_eq_gaussianShiftColeHopf f hf.1.continuous v x m)
  rw [he]
  exact boundedPositiveJets_gaussianShiftColeHopf hf _ m

end QuantitativeFollowup
