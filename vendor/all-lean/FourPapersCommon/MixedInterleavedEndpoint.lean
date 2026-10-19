module
public import FourPapersCommon.MixedInterleavedBounds

@[expose] public section

/-! Integration of the actual mixed tagged Gaussian derivative. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
open scoped BigOperators
namespace FourPapersCommon
variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

theorem deriv_mixedInterleavedInterpolationOffDiagonal_le
    {k n : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) (r : ℕ) {j : ℕ}
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) {t u v w : ℝ}
    (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    deriv (section5InterleavedInterpolationOffDiagonal n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U r j t u (ξ.clock v)) w ≤
      -2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v := by
  rw [(hasDerivAt_section5InterleavedInterpolationOffDiagonal_mixed hn ξ (mixedClockScheme ξ s)
    (mixedBeta ξ) h sk r hj0 hj ht (clock_mem_abs_interval ξ s hj hv) hw).deriv]
  let S:=mixedClockScheme ξ s
  let β:=mixedBeta ξ
  let N := 2 * k + 4 + 1
  let mode := section5ReverseMode S r j (decide (ξ.clock v < 0))
  let m := section5ReverseMass S r j
  let path := fun l => section5ReversePathVariance S β t (ξ.clock v) r j l w
  let ρ := section5InterleavedRho S r j |ξ.clock v|
  let a := fun l => β ^ 2 * (ρ (2 * k + 4 - l + 1) - ρ (2 * k + 4 - l))
  let Z := fun ω => Real.sqrt (w * t) • sk.U ω
  let R := fun ω => ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
    mixedConstrainedSecond mode m path N (Z ω) (sk.hU.w i) (sk.hU.w i) u
      (fun _ => h) (fun _ => h)
  let D := fun l : Fin N => fun ω => mixedLevelVarianceD (Z ω) u mode m path l
    (N - (l + 1)) (path l) (fun _ => h) (fun _ => h)
  have hm : ∀ l, 0 ≤ m l := section5ReverseMass_nonneg S r hj
  have hv0 : ∀ l, 0 ≤ path l := by
    intro l
    exact section5ReversePathVariance_nonneg S β ht hw.2.le r hj (clock_mem_abs_interval ξ s hj hv) l
  have hZ : Measurable Z := sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))
  have hiR : Integrable R := integrable_mixedConstrainedSecond_mixed_trace hn ξ sk hZ
    u mode m path hm hv0 N (fun _ => h) (fun _ => h)
  have hiD (l : Fin N) : Integrable (D l) := integrable_mixedLevelVarianceD_all_variances hn hZ
    u mode m path hm hv0 l (N - (l + 1)) (fun _ => h) (fun _ => h)
  have hiS : Integrable (fun ω => ∑ l : Fin N, a l * D l ω) :=
    integrable_finsetSum _ fun l _ => (hiD l).const_mul (a l)
  have hiI : Integrable (fun ω => (1 / (n : ℝ)) *
      (t / 2 * R ω - t * ∑ l : Fin N, a l * D l ω)) := by
    exact (hiR.const_mul (t / 2)).sub (hiS.const_mul t) |>.const_mul (1 / (n : ℝ))
  have hpoint (ω : Ω) :
      (1 / (n : ℝ)) * (t / 2 * R ω - t * ∑ l : Fin N, a l * D l ω) ≤
        -2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v := by
    simpa only [N, mode, m, path, ρ, a, Z, R, D, S, β,
      show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using
      mixedInterleaved_actualTraceHeat_offDiagonal_le hn ξ s h sk r hj0 hj u v ht hv
        hw.2.le (Z ω) (fun _ => h) (fun _ => h)
  calc
    _ ≤ ∫ _ : Ω, (-2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v) :=
      integral_mono hiI (integrable_const _) (fun ω => hpoint ω)
    _ = _ := by simp

theorem mixedInterleavedInterpolationOffDiagonal_endpoint_bound
    (hn : 0<n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) {r : ℕ} (hr0 : 1≤r) (hr : r≤k+1)
    {j : ℕ} (hj0 : 1≤j) (hj : j≤k+1) {t u v : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hv : |v|∈Icc (s.q (j-1)) (s.q j))
    [Nonempty (AT.ConstrainedPair n u)] :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u ≤
      section5InterleavedInterpolationOffDiagonal n (mixedClockScheme ξ s) (mixedBeta ξ)
        h sk.U r j t u (ξ.clock v) 0-2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v := by
  have hc:=continuousOn_section5InterleavedInterpolationOffDiagonal (u:=u)
    (mixedClockScheme ξ s) (mixedBeta ξ) h sk.hU r hj ht (clock_mem_abs_interval ξ s hj hv)
  have hd : DifferentiableOn ℝ
      (section5InterleavedInterpolationOffDiagonal n (mixedClockScheme ξ s) (mixedBeta ξ)
        h sk.U r j t u (ξ.clock v)) (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro w hw
    exact (hasDerivAt_section5InterleavedInterpolationOffDiagonal_mixed (u:=u) hn ξ
      (mixedClockScheme ξ s) (mixedBeta ξ) h sk r hj0 hj ht
      (clock_mem_abs_interval ξ s hj hv) hw).differentiableAt.differentiableWithinAt
  have hb : ∀w∈interior (Icc (0:ℝ) 1),
    deriv (section5InterleavedInterpolationOffDiagonal n (mixedClockScheme ξ s) (mixedBeta ξ)
      h sk.U r j t u (ξ.clock v)) w≤-2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v := by
    rw [interior_Icc]
    exact fun w hw=>deriv_mixedInterleavedInterpolationOffDiagonal_le hn ξ s h sk r hj0 hj ht hv hw
  have H:=(convex_Icc (0:ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hd hb
    0 (by simp) 1 (by simp) zero_le_one
  rw [section5InterleavedInterpolationOffDiagonal_one n (mixedClockScheme ξ s)
    (mixedBeta ξ) h sk.U hr0 hr j ht.2] at H
  simp only [sub_zero,mul_one] at H
  linarith

/-- Actual constrained mixed-model majorant for all signed trial intervals.
The trial covariance clock appears only in the Gaussian scalar recursion;
the physical constraint remains in the linear term and tangent remainder. -/
theorem mixed_constrainedPhi_le_interleavedOffDiagonalMajorant
    (hn : 0<n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) {r : ℕ} (hr0 : 1≤r) (hr : r≤k+1)
    {j : ℕ} (hj0 : 1≤j) (hj : j≤k+1) {t u v ell : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hv : |v|∈Icc (s.q (j-1)) (s.q j))
    (hatt : ∃σ τ:Config n,overlap n σ τ=u) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u ≤
      2*Real.log 2+section5InterleavedScalarV (mixedClockScheme ξ s) (mixedBeta ξ)
        h r j t (ξ.clock v) ell-ell*u-2*t*mixedSchemeCorrection ξ s+t*ξ.tangentRemainder u v := by
  obtain ⟨σ,τ,hστ⟩:=hatt
  letI : Nonempty (AT.ConstrainedPair n u):=⟨⟨(σ,τ),hστ⟩⟩
  have H:=mixedInterleavedInterpolationOffDiagonal_endpoint_bound (u:=u) hn ξ s h sk hr0 hr hj0 hj ht hv
  have H0:=section5InterleavedInterpolationOffDiagonal_zero_le_lambda hn (mixedClockScheme ξ s)
    (mixedBeta ξ) h sk.U r hj ht (clock_mem_abs_interval ξ s hj hv) ⟨σ,τ,hστ⟩ ell
  linarith

end FourPapersCommon
