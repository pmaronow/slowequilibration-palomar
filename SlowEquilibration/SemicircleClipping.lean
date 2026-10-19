-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.JacobiSemicircle
public import Mathlib.Topology.UniformSpace.Dini

/-! Genuine removal of logarithmic clipping in the actual semicircle law,
uniformly on every compact set of shifts. DCT handles the moving singularity;
Dini's theorem uses the proved whole-line continuity of the true potential. -/

@[expose] public section
namespace SlowEquilibration.SemicircleClipping

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter ContinuousMap
open scoped Topology
open ResolventDensity JacobiSemicircle SemicirclePotential SemicircleWholeLine SpectralTraceLipschitz
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

def clippedMap (k : ℝ) (rho : ℝ) (hrho : 0<rho) : C(K,ℝ) :=
  ⟨fun x => clippedLog k rho x.val,(clippedLog_lipschitz k hrho).continuous.comp continuous_subtype_val⟩

def clippedPotential (k rho : ℝ) : ℝ := ∫ t,clippedLog k rho t ∂SemicirclePotential.law

lemma clippedPotential_eq (k : ℝ) {rho : ℝ} (hrho : 0<rho) :
    clippedPotential k rho=probabilityIntegral semicircleLawOnK (clippedMap k rho hrho) := by
  exact (subtype_hasLaw.integral_comp (clippedLog_lipschitz k hrho).continuous.aestronglyMeasurable).symm

lemma clippedPotential_continuous {rho : ℝ} (hrho : 0<rho) :
    Continuous (fun k => clippedPotential k rho) := by
  let R : C(ℝ × K,ℝ) := ⟨fun p => clippedLog p.1 rho p.2.val,by
    unfold clippedLog
    apply Continuous.log
    · fun_prop
    · intro p
      exact ne_of_gt (lt_of_lt_of_le hrho (le_max_right _ _))⟩
  have he : (fun k => clippedPotential k rho)=
      (probabilityIntegral semicircleLawOnK) ∘ R.curry := by
    funext k
    exact clippedPotential_eq k hrho
  rw [he]
  exact (probabilityIntegral semicircleLawOnK).continuous.comp R.curry.continuous

lemma log_clipped_abs_le {d rho : ℝ} (hd : 0<d) (hrho : 0<rho) (hrho1 : rho≤1) :
    |Real.log (max d rho)|≤|Real.log d| := by
  by_cases h : rho≤d
  · rw [max_eq_left h]
  · have hdr : d<rho := lt_of_not_ge h
    rw [max_eq_right hdr.le]
    have hld : Real.log d≤0 := Real.log_nonpos hd.le (hdr.le.trans hrho1)
    have hlr : Real.log rho≤0 := Real.log_nonpos hrho.le hrho1
    rw [abs_of_nonpos hld,abs_of_nonpos hlr]
    exact neg_le_neg (Real.log_le_log hd hdr.le)

def clippingRadius (n : ℕ) : ℝ := 1/(n+1 : ℝ)

lemma clippingRadius_pos (n : ℕ) : 0<clippingRadius n := by unfold clippingRadius;positivity
lemma clippingRadius_le_one (n : ℕ) : clippingRadius n≤1 := by
  unfold clippingRadius
  apply (div_le_iff₀ (by positivity : 0<(n+1 : ℝ))).mpr
  norm_num
lemma clippingRadius_tendsto : Tendsto clippingRadius atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  exact hn.const_div_atTop 1

lemma clippingRadius_antitone : Antitone clippingRadius := by
  intro n m hnm
  unfold clippingRadius
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)

lemma scalar_clipping_limit (k t : ℝ) (hkt : k≠t) :
    Tendsto (fun n => clippedLog k (clippingRadius n) t) atTop (𝓝 (Real.log |k-t|)) := by
  unfold clippedLog
  have hd : |k-t|≠0 := abs_ne_zero.mpr (sub_ne_zero.mpr hkt)
  have hm := (tendsto_const_nhds (x := |k-t|)).max clippingRadius_tendsto
  have hm' : Tendsto (fun n => max |k-t| (clippingRadius n)) atTop (𝓝 |k-t|) := by
    simpa only [show max |k-t| (0:ℝ)=|k-t| from max_eq_left (abs_nonneg (k-t))] using hm
  exact Real.continuousAt_log hd |>.tendsto.comp hm'

lemma clippedPotential_tendsto (k : ℝ) :
    Tendsto (fun n => clippedPotential k (clippingRadius n)) atTop (𝓝 (potential k)) := by
  let _ : NullSingletonClass SemicirclePotential.law := by
    unfold SemicirclePotential.law
    infer_instance
  have hae : ∀ᵐ t ∂SemicirclePotential.law,k≠t := by simpa only [ne_comm] using SemicirclePotential.law.ae_ne k
  have hmeas (n : ℕ) : AEStronglyMeasurable (clippedLog k (clippingRadius n)) SemicirclePotential.law :=
    (clippedLog_lipschitz k (clippingRadius_pos n)).continuous.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ t ∂SemicirclePotential.law,
      ‖clippedLog k (clippingRadius n) t‖≤|Real.log (|k-t|)| := by
    filter_upwards [hae] with t ht
    exact log_clipped_abs_le (abs_pos.mpr (sub_ne_zero.mpr ht))
      (clippingRadius_pos n) (clippingRadius_le_one n)
  have hlim : ∀ᵐ t ∂SemicirclePotential.law,
      Tendsto (fun n => clippedLog k (clippingRadius n) t) atTop (𝓝 (Real.log |k-t|)) := by
    filter_upwards [hae] with t ht
    exact scalar_clipping_limit k t ht
  exact tendsto_integral_of_dominated_convergence _ hmeas (log_abs_integrable k).abs hbound hlim

lemma clippedPotential_antitone (k : ℝ) : Antitone (fun n => clippedPotential k (clippingRadius n)) := by
  intro n m hnm
  have hi (n : ℕ) : Integrable (clippedLog k (clippingRadius n)) SemicirclePotential.law := by
    have hf := continuous_test_integrable semicircleLawOnK (clippedMap k (clippingRadius n) (clippingRadius_pos n))
    rw [← subtype_hasLaw.map_eq]
    exact (integrable_map_measure (clippedLog_lipschitz k (clippingRadius_pos n)).continuous.aestronglyMeasurable
      measurable_subtype_coe.aemeasurable).mpr hf
  exact integral_mono (hi m) (hi n) fun t =>
    Real.log_le_log (lt_of_lt_of_le (clippingRadius_pos m) (le_max_right _ _))
      (max_le_max le_rfl (clippingRadius_antitone hnm))

/-- Logarithmic clipping disappears uniformly on every compact shift set,
with the true density-defined potential as the limit. -/
theorem clippedPotential_uniform_on_compact {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n k => clippedPotential k (clippingRadius n)) potential atTop S :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto hS
    (fun n => (clippedPotential_continuous (clippingRadius_pos n)).continuousOn)
    (fun k _hk => clippedPotential_antitone k) potential_continuous.continuousOn
    (fun k _hk => clippedPotential_tendsto k)

end
end SlowEquilibration.SemicircleClipping
