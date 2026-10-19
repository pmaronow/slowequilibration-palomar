-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPhysicalWindowRelativeComparison
public import Mathlib.Topology.Order.LiminfLimsup

/-! Literal maximum and all-critical-point count limits in fixed
physical-energy windows, including a true all-dimensional mean bound. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter TwoAtomStationarity SphericalModel
open GOEMaximumDeterminant
open scoped Topology
set_option maxHeartbeats 300000

theorem sourceMaximumWindowMean_limit_of_tail_limits (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R) (m : ℕ → ℝ)
    (htail : ∀ t : ℝ,Tendsto (fun n : ℕ => sourceMaximumEnergyTail n μ Q (Ioo L R) (m n+t))
      atTop (𝓝 (Real.exp (-(β*x)*t)))) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n : ℕ => sourceMaximumWindowMean n μ Q (Ioo L R) (m n+a) (m n+b))
      atTop (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) := by
  have ht := (htail a).sub (htail b)
  have he : (fun n : ℕ => sourceMaximumEnergyTail n μ Q (Ioo L R) (m n+a)-
      sourceMaximumEnergyTail n μ Q (Ioo L R) (m n+b))=ᶠ[atTop]
      (fun n : ℕ => sourceMaximumWindowMean n μ Q (Ioo L R) (m n+a) (m n+b)) := by
    filter_upwards [sourceMaximumWindowMean_eq_tail_difference μ h hnp hL hm] with n hn
    exact (hn (m n+a) (m n+b) (by linarith)).symm
  exact ht.congr' he

theorem sourceCriticalWindowMean_limit_of_maximum_limit (μ : FiniteMixture) {Q L R z : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hL : sourceRadialEdge μ Q < L)
    (l r : ℕ → ℝ)
    (hmax : Tendsto (fun n : ℕ => sourceMaximumWindowMean n μ Q (Ioo L R) (l n) (r n)) atTop (𝓝 z)) :
    Tendsto (fun n : ℕ => sourceCriticalWindowMean n μ Q (Ioo L R) (l n) (r n)) atTop (𝓝 z) := by
  obtain ⟨C,_hC,herror,hbound⟩ := sourceWindowMean_relative_comparison μ hQ hnp hL (R := R)
  have hupper : Tendsto (fun n : ℕ => sourceMaximumWindowMean n μ Q (Ioo L R) (l n) (r n)/
      (1-maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n)) atTop (𝓝 z) := by
    simpa only [sub_zero,div_one,Pi.div_def,Pi.sub_def] using hmax.div (tendsto_const_nhds.sub herror) (by norm_num : (1 : ℝ)-0 ≠ 0)
  apply hmax.squeeze' hupper
  · filter_upwards [hbound] with n hn
    exact (hn.2.2 (l n) (r n)).2
  · filter_upwards [hbound] with n hn
    apply (le_div_iff₀ (sub_pos.mpr hn.2.1)).mpr
    exact (mul_comm _ _).trans_le (hn.2.2 (l n) (r n)).1

theorem sourceWindowMeans_uniformly_bounded_of_limits (nmax nall : ℕ → ℝ) {z : ℝ}
    (hmax : Tendsto nmax atTop (𝓝 z)) (hall : Tendsto nall atTop (𝓝 z)) :
    ∃ C : ℝ,0 < C ∧ ∀ n : ℕ,nmax n ≤ C ∧ nall n ≤ C := by
  obtain ⟨Bmax,hBmax⟩ := hmax.bddAbove_range
  obtain ⟨Ball,hBall⟩ := hall.bddAbove_range
  let C := max 1 (max Bmax Ball)
  refine ⟨C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro n
  constructor
  · exact (hBmax (mem_range_self n)).trans ((le_max_left Bmax Ball).trans (le_max_right _ _))
  · exact (hBall (mem_range_self n)).trans ((le_max_right Bmax Ball).trans (le_max_right _ _))

end SlowEquilibration.SphericalMarkedWindows
