-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianJet
public import SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.EdgeAsymptotics

@[expose] public section

/-!
# Genuine GOE spectral asymptotics

The explicit GOE matrix law of `SphericalGaussianJet` is identified with the
actual orthogonally invariant Gaussian law in the pinned OpenAI proof provider.
That provider derives tridiagonal reduction, spectral comparison and Jacobi
resolvent estimates. The asymptotic estimates below use those proofs, rather
than taking a semicircle law or spectral barrier as a premise.
-/

namespace SlowEquilibration.GOEAsymptotics

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
open OAI.CriticalSK

abbrev GaussianMatrix (k : ℕ) := OAI.CriticalSK.GaussianMatrix (Fin k)

def matrixToGaussian {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ) : GaussianMatrix k :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => W i j))

def gaussianToMatrix {k : ℕ} (W : GaussianMatrix k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => W i j

theorem matrixToGaussian_measurable (k : ℕ) : Measurable (matrixToGaussian (k := k)) := by
  unfold matrixToGaussian
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  exact (measurable_pi_apply j).comp (measurable_pi_apply i)

theorem gaussianToMatrix_measurable (k : ℕ) : Measurable (gaussianToMatrix (k := k)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) j).measurable.comp
    (PiLp.continuous_apply 2 (fun _ : Fin k => EuclideanSpace ℝ (Fin k)) i).measurable

@[simp] theorem matrixToGaussian_gaussianToMatrix {k : ℕ} (W : GaussianMatrix k) :
    matrixToGaussian (gaussianToMatrix W) = W := by ext i j; rfl

@[simp] theorem gaussianToMatrix_matrixToGaussian {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ) :
    gaussianToMatrix (matrixToGaussian W) = W := rfl

/-- Exact agreement of the two explicit GOE constructions. The upstream
parameter `sigma` gives off-diagonal variance `2 sigma^2`. -/
theorem goeLaw_bridge (k N : ℕ) (s sigma : ℝ) (hscale : 2 * sigma ^ 2 = s / (N : ℝ)) :
    (SphericalGaussianJet.goeLaw k N s).map matrixToGaussian =
      OAI.CriticalSK.goeLaw (Fin k) sigma := by
  classical
  rw [OAI.CriticalSK.goeLaw_eq_upper_product]
  unfold SphericalGaussianJet.goeLaw
  rw [Measure.map_map (matrixToGaussian_measurable k) (SphericalGaussianJet.symmetricMatrix_measurable k)]
  have hmarg : (fun ij : SphericalGaussianJet.UpperIndex k => gaussianReal 0
        (((s / (N : ℝ)) * (if ij.val.1 = ij.val.2 then 2 else 1)).toNNReal)) =
      (fun ij : OAI.CriticalSK.UpperEntry (Fin k) => gaussianReal 0
        (if ij.val.1 = ij.val.2 then (4 * sigma ^ 2).toNNReal else (2 * sigma ^ 2).toNNReal)) := by
    funext ij
    split_ifs
    · congr 1
      apply congrArg Real.toNNReal
      rw [← hscale]
      ring
    · simp [hscale]
  rw [hmarg]
  rfl

/-- The normalization of the manuscript's standard GOE is exactly the
normalization in the upstream spectral proof. -/
theorem normalized_goeLaw_bridge (n : ℕ) :
    (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).map matrixToGaussian =
      OAI.CriticalSK.goeLaw (Fin (n + 1)) (goeScale n) := by
  apply goeLaw_bridge
  simpa only [one_div, Nat.cast_add, Nat.cast_one] using goeScale_square n

/-- Actual ordered eigenvalues of the actual symmetric matrix, extended
continuously to all matrices by the upstream symmetrization convention. -/
def eigenvalues (n : ℕ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin (n + 1) → ℝ :=
  matrixOrderedEigenvalues (matrixToGaussian W)

theorem eigenvalues_measurable (n : ℕ) : Measurable (eigenvalues n) :=
  (matrixOrderedEigenvalues_measurable (n + 1)).comp (matrixToGaussian_measurable (n + 1))

def empiricalResolvent (n : ℕ) (s : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  (∑ i, (2 + s - eigenvalues n W i)⁻¹) / (n + 1)

theorem traceCost_fixed_tendsto {h s : ℝ} (hh : 0 ≤ h) (_hs : 0 < s) :
    Tendsto (fun n => traceCost n h s) atTop (𝓝 0) := by
  have hA := ((formA_tendsto hh).const_mul 416).mul_const (s ^ (-5 / 8 : ℝ))
  have hB := (formB_tendsto.const_mul 8).div_const s
  have hC := (formC_tendsto.const_mul 2).div_const (Real.sqrt s)
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have htail := (hn.const_div_atTop 2).div_const (s * Real.sqrt s)
  have htail' : Tendsto (fun n : ℕ => 2 / ((n + 1 : ℝ) * s * Real.sqrt s)) atTop (𝓝 0) := by
    simpa [div_div, mul_assoc] using htail
  simpa only [traceCost, mul_zero, zero_mul, zero_div, zero_add, add_zero] using ((hA.add hB).add hC).add htail'

def goodEvent (n : ℕ) (h s : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  (eigenvalues n) ⁻¹' spectralGood n h s

theorem goodEvent_measurable (n : ℕ) (h s : ℝ) : MeasurableSet (goodEvent n h s) :=
  (spectralGood_measurable n h s).preimage (eigenvalues_measurable n)

/-- Quantitative genuine GOE probability bound transferred across the exact
law identification, with all finite spectral-comparison conditions explicit. -/
theorem goodEvent_failure_probability (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s)
    (hscale : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s)
    (hsmall : formA n h * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + formC n ≤ 1) :
    (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (goodEvent n h s)ᶜ ≤
      32 * Real.exp (-h ^ 2) := by
  have hmap : HasLaw (matrixToGaussian (k := n + 1))
      (OAI.CriticalSK.goeLaw (Fin (n + 1)) (goeScale n))
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) :=
    ⟨(matrixToGaussian_measurable _).aemeasurable, normalized_goeLaw_bridge n⟩
  have hset : MeasurableSet ((matrixOrderedEigenvalues (n := n + 1)) ⁻¹'
      (spectralGood n h s)ᶜ) :=
    (spectralGood_measurable n h s).compl.preimage (matrixOrderedEigenvalues_measurable _)
  have heq := hmap.measureReal_eq hset
  have hprob := goe_spectral_bad_probability n hh hs hscale hsmall
  have hleft : {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ |
      matrixOrderedEigenvalues (matrixToGaussian W) ∈ (spectralGood n h s)ᶜ} =
      (goodEvent n h s)ᶜ := rfl
  have hright : {W : GaussianMatrix (n + 1) |
      matrixOrderedEigenvalues W ∈ (spectralGood n h s)ᶜ} =
      matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ := rfl
  rw [hleft, hright] at heq
  exact heq.le.trans hprob

def resolventBad (n : ℕ) (s eps : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  {W | eps < |empiricalResolvent n s W - semicircleResolvent s|}

/-- All finite spectral-comparison conditions follow eventually from the
proved deterministic asymptotics. No spectral barrier or semicircle limit is
an input to this actual GOE resolvent probability estimate. -/
theorem resolvent_bad_probability_eventually {h s eps : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (resolventBad n s eps) ≤
        32 * Real.exp (-h ^ 2) := by
  let s₀ := min s 1
  let eta := min (eps / (2 * Real.sqrt s)) (1 / 5)
  have hs₀ : 0 < s₀ := lt_min hs (by norm_num)
  have hs₀s : s₀ ≤ s := min_le_left _ _
  have hs₀1 : s₀ ≤ 1 := min_le_right _ _
  have heta : 0 < eta := lt_min (div_pos heps (by positivity)) (by norm_num)
  have heta1 : eta ≤ 1 / 5 := min_le_right _ _
  have hetaeps : eta * Real.sqrt s < eps := by
    have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have h := mul_le_mul_of_nonneg_right (min_le_left (eps / (2 * Real.sqrt s)) (1 / 5)) hroot.le
    have heq : (eps / (2 * Real.sqrt s)) * Real.sqrt s = eps / 2 := by
      field_simp
    rw [heq] at h
    exact h.trans_lt (by linarith)
  have hcost := (traceCost_fixed_tendsto hh hs₀).eventually (gt_mem_nhds heta)
  have hbase := (naturalEdgeScale_tendsto 1).eventually (gt_mem_nhds hs₀)
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hspace := ((hn.atTop_mul_const hs₀).atTop_mul_const (Real.sqrt_pos.mpr hs₀)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [hcost, hbase, hspace] with n hcost hbase hspace
  have hsum := traceCost_small n hh hs₀ hs₀1 hcost.le
  have hscale : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s₀ :=
    (naturalEdgeScale_base n (L := 1) le_rfl).trans hbase.le
  have hsmall : formA n h * s₀ ^ (-5 / 8 : ℝ) + formB n / s₀ + formC n ≤ 1 / 2 := by
    linarith
  have hsmall' : formA n h * (3 / 8 : ℝ) * s₀ ^ (-5 / 8 : ℝ) + formC n ≤ 1 := by
    have hA : 0 ≤ formA n h * s₀ ^ (-5 / 8 : ℝ) :=
      mul_nonneg (formA_nonneg n hh) (Real.rpow_nonneg hs₀.le _)
    have hB : 0 ≤ formB n / s₀ := div_nonneg (formB_nonneg _) hs₀.le
    nlinarith
  have hsub : resolventBad n s eps ⊆ (goodEvent n h s₀)ᶜ := by
    intro W hW hgood
    have htrace := spectralGood_relative_trace n hh hs₀ hs₀s hsmall hspace hgood hcost.le
    exact (not_lt_of_ge (htrace.trans hetaeps.le)) hW
  exact (measureReal_mono hsub).trans (goodEvent_failure_probability n hh hs₀ hscale hsmall')

theorem goodEvent_failure_probability_eventually {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop,
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (goodEvent n h s)ᶜ ≤
        32 * Real.exp (-h ^ 2) := by
  have hbase := (naturalEdgeScale_tendsto 1).eventually (gt_mem_nhds hs)
  have hsmall := (((formA_tendsto hh).mul_const (3 / 8 : ℝ)).mul_const (s ^ (-5 / 8 : ℝ))).add
    formC_tendsto
  have hsmall' : Tendsto (fun n => formA n h * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + formC n)
      atTop (𝓝 0) := by simpa only [zero_mul, zero_add] using hsmall
  filter_upwards [hbase, hsmall'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hbase hsmall
  exact goodEvent_failure_probability n hh hs
    ((naturalEdgeScale_base n (L := 1) le_rfl).trans hbase.le) hsmall.le

def edgeBad (n : ℕ) (eps : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  {W | ∃ i, 2 + eps < |eigenvalues n W i|}

/-- The entire actual GOE spectrum lies in the semicircle support enlarged
by any fixed positive amount with probability tending to one. This finite
bound proves both spectral edges, without an edge-barrier premise. -/
theorem edge_bad_probability_eventually {h eps : ℝ} (hh : 0 ≤ h) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (edgeBad n eps) ≤
        32 * Real.exp (-h ^ 2) := by
  let eta := min (eps / 10) (1 / 5)
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have hetaeps : 5 * eta < eps := by
    have h := min_le_left (eps / 10) (1 / 5)
    change eta ≤ eps / 10 at h
    linarith
  have hcost := (traceCost_fixed_tendsto hh (by norm_num : (0 : ℝ) < 1)).eventually (gt_mem_nhds heta)
  filter_upwards [hcost, goodEvent_failure_probability_eventually hh (by norm_num : (0 : ℝ) < 1)]
    with n hcost hprob
  have hsub : edgeBad n eps ⊆ (goodEvent n h 1)ᶜ := by
    rintro W ⟨i, hi⟩ hgood
    have hdiff := spectralGood_relative_error n hh (by norm_num : (0 : ℝ) < 1) le_rfl
      hcost.le hgood i
    have hgap0 := orderedJacobiGaps_nonneg n i
    have hgap4 := orderedJacobiGaps_le_four n i
    have heta0 := heta.le
    have hdiff' : |eigenvalues n W i - (2 - orderedJacobiGaps n i)| ≤ 5 * eta := by
      exact hdiff.trans (by nlinarith)
    have hjac : |2 - orderedJacobiGaps n i| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have htri : |eigenvalues n W i| ≤
        |eigenvalues n W i - (2 - orderedJacobiGaps n i)| + |2 - orderedJacobiGaps n i| := by
      convert abs_add_le (eigenvalues n W i - (2 - orderedJacobiGaps n i))
        (2 - orderedJacobiGaps n i) using 1
      ring
    have habs := htri.trans
      (add_le_add hdiff' hjac)
    linarith
  exact (measureReal_mono hsub).trans hprob

/-- A real nonnegative sequence with the proved arbitrarily small Gaussian
tail envelope converges to zero. -/
theorem tendsto_zero_of_gaussian_tail_envelope {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n)
    (hbound : ∀ h : ℝ, 0 ≤ h → ∀ᶠ n : ℕ in atTop, p n ≤ 32 * Real.exp (-h ^ 2)) :
    Tendsto p atTop (𝓝 0) := by
  have htail : Tendsto (fun h : ℝ => 32 * Real.exp (-h ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_pow_atTop two_ne_zero)).const_mul 32
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨h, hh, htail⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (htail.eventually (gt_mem_nhds heps))).exists
  filter_upwards [hbound h hh] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hp n)] using hn.trans_lt htail

/-- Actual dimension-dependent GOE resolvent convergence in probability to
the semicircle resolvent at every fixed argument strictly above the edge. -/
theorem empirical_resolvent_converges_in_probability {s eps : ℝ} (hs : 0 < s) (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (resolventBad n s eps))
      atTop (𝓝 0) :=
  tendsto_zero_of_gaussian_tail_envelope (fun _ => measureReal_nonneg)
    (fun _ hh => resolvent_bad_probability_eventually hh hs heps)

/-- Actual GOE spectral confinement to `[-2-eps, 2+eps]` in probability. -/
theorem spectrum_converges_to_semicircle_support {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (edgeBad n eps))
      atTop (𝓝 0) :=
  tendsto_zero_of_gaussian_tail_envelope (fun _ => measureReal_nonneg)
    (fun _ hh => edge_bad_probability_eventually hh heps)

end
end SlowEquilibration.GOEAsymptotics
