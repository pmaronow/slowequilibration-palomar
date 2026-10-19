-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairWindowCountIdentity
public import SlowEquilibration.SourcePairOverlapAnnulusRates

/-! ENNReal comparison on the actual sphere product probability law.
The comparison needs no measurability premise about selected tangent frames. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows SphereChartVolume
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma sphere_pair_round_lintegral_eq (n:ℕ) (f:Vector (n+3)×Vector (n+3)→ℝ≥0∞) :
    (∫⁻ p,f p ∂(manuscriptRoundVolume (n+2)).prod (manuscriptRoundVolume (n+2)))=
      ∫⁻ p,(manuscriptRoundVolume (n+2) univ)^2*f p ∂(sphereLaw (n+3)).prod (sphereLaw (n+3)):=by
  conv_lhs => rw [manuscriptRoundVolume_eq_area_sphereLaw,Measure.prod_smul_left,Measure.prod_smul_right,
    lintegral_smul_measure,lintegral_smul_measure]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (manuscriptRoundVolume_mass_ne_top (n+2)))]
  simp only [smul_eq_mul]
  ring

lemma sphere_pair_supported (n:ℕ) :
    ∀ᵐ p:Vector (n+3)×Vector (n+3) ∂(sphereLaw (n+3)).prod (sphereLaw (n+3)),
      ‖p.1‖^2=(n+3:ℕ) ∧ ‖p.2‖^2=(n+3:ℕ):=by
  have hSupport:=SphericalAging.SphereInitialLaw.sphereLaw_support (N:=n+3) (by omega)
  exact (Measure.quasiMeasurePreserving_fst.ae hSupport).and
    (Measure.quasiMeasurePreserving_snd.ae hSupport)

lemma sphere_pair_integral_central_bound (n:ℕ) (δ:ℝ)
    (f:Vector (n+3)×Vector (n+3)→ℝ≥0∞) (B:ℝ≥0∞)
    (hPoint:∀ (x y:Vector (n+3)),‖x‖^2=(n+3:ℕ) → ‖y‖^2=(n+3:ℕ) →
      |overlap x y|<δ → (manuscriptRoundVolume (n+2) univ)^2*f (x,y) ≤ B) :
    (∫⁻ p,{p:Vector (n+3)×Vector (n+3)| |overlap p.1 p.2|<δ}.indicator f p
      ∂(manuscriptRoundVolume (n+2)).prod (manuscriptRoundVolume (n+2))) ≤ B:=by
  rw [sphere_pair_round_lintegral_eq]
  calc
    _ ≤ ∫⁻ _p:Vector (n+3)×Vector (n+3),B ∂(sphereLaw (n+3)).prod (sphereLaw (n+3)):=by
      apply lintegral_mono_ae
      filter_upwards [sphere_pair_supported n] with p hp
      by_cases hr:|overlap p.1 p.2|<δ
      · simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_left hr]
        exact hPoint p.1 p.2 hp.1 hp.2 hr
      · simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_right hr,mul_zero,zero_le]
    _ = B:=by simp

lemma sphere_pair_integral_subcritical_bound (n:ℕ) (δ t:ℝ)
    (f:Vector (n+3)×Vector (n+3)→ℝ≥0∞) (B C W:ℝ≥0∞) (hW:W≠⊤)
    (hPointCentral:∀ (x y:Vector (n+3)),‖x‖^2=(n+3:ℕ) → ‖y‖^2=(n+3:ℕ) →
      |overlap x y| ≤ t → (manuscriptRoundVolume (n+2) univ)^2*f (x,y) ≤ B*W)
    (hPointLocal:∀ (x y:Vector (n+3)),‖x‖^2=(n+3:ℕ) → ‖y‖^2=(n+3:ℕ) →
      |overlap x y|<δ → (manuscriptRoundVolume (n+2) univ)^2*f (x,y) ≤
        C*ENNReal.ofReal (Real.exp (((n+3:ℕ):ℝ)*(overlap x y)^2/8))*W) :
    (∫⁻ p,{p:Vector (n+3)×Vector (n+3)| |overlap p.1 p.2|<δ}.indicator f p
      ∂(manuscriptRoundVolume (n+2)).prod (manuscriptRoundVolume (n+2))) ≤
      (B+C*(∫⁻ p:Vector (n+3)×Vector (n+3),
        {p:Vector (n+3)×Vector (n+3)|t < |overlap p.1 p.2|}.indicator
          (fun p=>ENNReal.ofReal (Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8))) p
        ∂(sphereLaw (n+3)).prod (sphereLaw (n+3))))*W:=by
  let T:={p:Vector (n+3)×Vector (n+3)|t < |overlap p.1 p.2|}
  let G:=fun p:Vector (n+3)×Vector (n+3)=>ENNReal.ofReal (Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8))
  have hT:MeasurableSet T:=measurableSet_lt measurable_const (by unfold overlap;fun_prop)
  have hG:Measurable G:=by unfold G overlap;fun_prop
  rw [sphere_pair_round_lintegral_eq]
  calc
    _ ≤ ∫⁻ p:Vector (n+3)×Vector (n+3),B*W+C*(T.indicator G p)*W
        ∂(sphereLaw (n+3)).prod (sphereLaw (n+3)):=by
      apply lintegral_mono_ae
      filter_upwards [sphere_pair_supported n] with p hp
      by_cases hr:|overlap p.1 p.2|<δ
      · simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_left hr]
        by_cases ht:|overlap p.1 p.2| ≤ t
        · exact (hPointCentral p.1 p.2 hp.1 hp.2 ht).trans (le_add_right le_rfl)
        · have htp:p∈T:=lt_of_not_ge ht
          rw [ite_eq_left htp]
          exact (hPointLocal p.1 p.2 hp.1 hp.2 hr).trans (le_add_left le_rfl)
      · simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_right hr,mul_zero,zero_le]
    _ = (B+C*(∫⁻ p,T.indicator G p ∂(sphereLaw (n+3)).prod (sphereLaw (n+3))))*W:=by
      rw [lintegral_add_left measurable_const]
      simp_rw [lintegral_mul_const' _ _ hW]
      rw [lintegral_const_mul _ (hG.indicator hT)]
      simp only [lintegral_const,measure_univ,mul_one,add_mul]

end
end SlowEquilibration.PairConditionalDeterminantMoments
