-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxWindowCountBridge
public import SlowEquilibration.SourcePureLocalMaxIntensityTransfer

/-! Uniform exponentially accurate comparison of the original pure
all-critical and negative-Hessian local-maximum physical intensities on
the source exterior radial-mark interval. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter TwoAtomStationarity SphericalTAPCertificate
open GOEMaximumDeterminant GOEPhysicalNormalizedMoments GOEPhysicalPotential
open scoped Topology
set_option maxHeartbeats 400000

theorem sourcePure_critical_localMax_physical_comparison
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) {l r g Z : ℝ} (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ H ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r),
        (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal ≤
          (1+C*Real.exp (-c*(n+2 : ℕ)))*
            (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal := by
  let μ := FiniteMixture.pure p hp a ha
  let b := Q^2*μ.xi2 Q
  have hb : 0 < b := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨C,c,hC,hc,hComp⟩ := maximumMean_relative_comparison (Z := Z) hb hg
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [hComp] with n hn
  intro H hH
  let N : ℝ := (n+2 : ℕ)
  let e : ℝ := H/N
  let k : ℝ := (p : ℝ)*H/N
  let d : ℝ := 1+C*Real.exp (-c*N)
  let A : ℝ := (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal
  let M : ℝ := (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal
  let P : ℝ := physicalMean n (n+2) b k
  let X : ℝ := maximumMean n (n+2) b k
  have hN : 0 < N := by dsimp [N]; positivity
  have he : e ∈ Ioo l r := by
    dsimp [e]
    constructor
    · apply (lt_div_iff₀ hN).mpr
      nlinarith [hH.1]
    · apply (div_lt_iff₀ hN).mpr
      nlinarith [hH.2]
  have hke : k = (p : ℝ)*e := by dsimp [k,e]; ring
  have hk : k ∈ Icc (2*Real.sqrt b+g) Z := by
    constructor
    · have hh := mul_le_mul_of_nonneg_left he.1.le hp0.le
      rw [hke]
      dsimp [b,μ] at *
      linarith [hLeft]
    · have hh := mul_le_mul_of_nonneg_left he.2.le hp0.le
      rw [hke]
      dsimp [b,μ] at *
      linarith [hRight]
  have hEdge : 2*Real.sqrt b < k := lt_of_lt_of_le (by linarith [hg]) hk.1
  have hA : 0 < A := pureCriticalPhysicalIntensity_toReal_pos n p hp a ha hQ H hEdge
  have hP : 0 < P := physicalMean_pos n 1 hb hEdge
  have hRatio := pureLocalMaxPhysicalIntensity_div_critical n p hp a ha hQ H hEdge
  change M/A=X/P at hRatio
  have hCross : M*P=A*X := by
    calc
      M*P=X*A := (div_eq_div_iff hA.ne' hP.ne').mp hRatio
      _ = A*X := mul_comm _ _
  have hCompare : P ≤ d*X := hn k hk
  have hMul : A*P ≤ d*M*P := by
    calc
      A*P ≤ A*(d*X) := mul_le_mul_of_nonneg_left hCompare hA.le
      _ = d*M*P := by calc
        A*(d*X) = d*(A*X) := by ring
        _ = d*(M*P) := by rw [←hCross]
        _ = d*M*P := by ring
  change A ≤ d*M
  by_contra hnot
  have hdiff : 0 < A-d*M := sub_pos.mpr (lt_of_not_ge hnot)
  have hprod := mul_pos hdiff hP
  nlinarith [hMul]

end SlowEquilibration.SphericalMarkedWindows
