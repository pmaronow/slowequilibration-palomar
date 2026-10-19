-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureSemicircleExteriorLipschitz
public import SlowEquilibration.SourcePureOnePointSignedMeanTransfer
public import SlowEquilibration.GOEPhysicalNormalizedMoments

/-! Transfer the proper-pure source contact tangent from the signed Hermite
weight to the actual absolute GOE determinant mean in the one-point
Kac--Rice intensity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter GOEPhysicalPotential GOEPhysicalSignedMean
open GOEPhysicalNormalizedMoments GOEPureSignedMaximumTransfer
open GOEClippedResolvent TwoAtomStationarity SphericalTAPCertificate
open scoped Topology
set_option maxHeartbeats 500000

/-- The logarithms of the actual absolute determinant mean and the signed
Hermite mean agree asymptotically on every compact exterior GOE shift
sequence. Both are genuine finite-dimensional Gaussian expectations. -/
theorem signed_actual_log_mean_agree {b g Z : ℝ}
    (hb : 0 < b) (hg : 0 < g) (k : ℕ → ℝ)
    (hk : ∀ᶠ n : ℕ in atTop, k n ∈ Icc (2*Real.sqrt b+g) Z) :
    Tendsto (fun n : ℕ =>
      Real.log (physicalMean n (n+2) b (k n))-
        Real.log (signedPhysicalMean (n+1) (n+2) b (k n)))
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨C,c,hC,hc,hLoss⟩ :=
    signedPhysicalMean_absoluteMean_relative_loss (Z := Z) hb hg
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun n : ℕ => C*Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (0 : ℝ)) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hN.atTop_mul_const hc)
    convert hh.const_mul C using 1
    · funext n
      simp only [Function.comp_def]
      congr 1
      ring
    · ring
  have hRatioError : Tendsto (fun n : ℕ =>
      signedPhysicalMean (n+1) (n+2) b (k n)/physicalMean n (n+2) b (k n)-1)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm' _ hExp
    filter_upwards [hk,hLoss] with n hn hln
    have hEdge : 2*Real.sqrt b < k n := by linarith [hn.1]
    have hA : 0 < physicalMean n (n+2) b (k n) := physicalMean_pos n 1 hb hEdge
    have hLoss' := hln (k n) hn
    have hEq :
        |signedPhysicalMean (n+1) (n+2) b (k n)/
            physicalMean n (n+2) b (k n)-1| =
          |physicalMean n (n+2) b (k n)-
            signedPhysicalMean (n+1) (n+2) b (k n)|/
              physicalMean n (n+2) b (k n) := by
      rw [show signedPhysicalMean (n+1) (n+2) b (k n)/
          physicalMean n (n+2) b (k n)-1 =
            (signedPhysicalMean (n+1) (n+2) b (k n)-
              physicalMean n (n+2) b (k n))/physicalMean n (n+2) b (k n) by
                field_simp]
      rw [abs_div,abs_sub_comm,abs_of_pos hA]
    rw [Real.norm_eq_abs,hEq]
    exact (div_le_iff₀ hA).mpr (by nlinarith [hLoss'])
  have hRatio : Tendsto (fun n : ℕ =>
      signedPhysicalMean (n+1) (n+2) b (k n)/physicalMean n (n+2) b (k n))
      atTop (𝓝 (1 : ℝ)) := by
    have hh := hRatioError.add (tendsto_const_nhds (x := (1 : ℝ)))
    simpa only [sub_add_cancel,zero_add] using hh
  have hLogRatio := hRatio.log one_ne_zero
  have hLogEq : (fun n : ℕ =>
      Real.log (signedPhysicalMean (n+1) (n+2) b (k n)/
        physicalMean n (n+2) b (k n))) =ᶠ[atTop]
      (fun n : ℕ => Real.log (signedPhysicalMean (n+1) (n+2) b (k n))-
        Real.log (physicalMean n (n+2) b (k n))) := by
    filter_upwards [hk] with n hn
    have hEdge : 2*Real.sqrt b < k n := by linarith [hn.1]
    have hA : 0 < physicalMean n (n+2) b (k n) := physicalMean_pos n 1 hb hEdge
    have hS : 0 < signedPhysicalMean (n+1) (n+2) b (k n) :=
      signedPhysicalMean_pos n (by omega) (by omega) hb hEdge
    exact Real.log_div hS.ne' hA.ne'
  have hLogs : Tendsto (fun n : ℕ =>
      Real.log (signedPhysicalMean (n+1) (n+2) b (k n))-
        Real.log (physicalMean n (n+2) b (k n))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.log_one] using hLogRatio.congr' hLogEq
  have hh := hLogs.neg
  simpa only [neg_sub,neg_zero] using hh

/-- Genuine absolute-mean physical-energy log-weight of a pure source. -/
def pureActualEnergyLogWeight (n : ℕ) (V b p H : ℝ) : ℝ :=
  -H^2/(2*(n+2 : ℕ)*V)+
    Real.log (physicalMean n (n+2) b (p*H/(n+2 : ℕ)))

theorem pureActualEnergyLogWeight_sub_signed (n : ℕ) (V b p H : ℝ) :
    pureActualEnergyLogWeight n V b p H-pureSignedEnergyLogWeight n V b p H =
      Real.log (physicalMean n (n+2) b (p*H/(n+2 : ℕ)))-
        Real.log (signedPhysicalMean (n+1) (n+2) b (p*H/(n+2 : ℕ))) := by
  unfold pureActualEnergyLogWeight pureSignedEnergyLogWeight
  ring

/-- The actual absolute physical GOE mean has the proper-pure contact
exponential along every source logarithmic centering. No replacement of
the absolute determinant by a signed proxy remains in this conclusion. -/
theorem sourcePure_actualEnergyLogWeight_log_window_tangent
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    Tendsto (fun n : ℕ =>
      pureActualEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n)-
        pureActualEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E)+β*x*σ n)
      atTop (𝓝 (0 : ℝ)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  let g := ((p : ℝ)*E-2*Real.sqrt b)/2
  let k : ℕ → ℝ := fun n => (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ)
  have hb : 0 < b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hContact : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hg : 0 < g := by dsimp [g]; linarith
  have hLower : 2*Real.sqrt b+g < (p : ℝ)*E := by dsimp [g]; linarith
  have hUpper : (p : ℝ)*E < (p : ℝ)*E+1 := by linarith
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hk : Tendsto k atTop (𝓝 ((p : ℝ)*E)) := by
    have hh := ((tendsto_const_nhds (x := E)).add hσzero).const_mul (p : ℝ)
    convert hh using 1
    · funext n
      dsimp [k]
      field_simp
    · ring
  have hkRange : ∀ᶠ n : ℕ in atTop,
      k n ∈ Icc (2*Real.sqrt b+g) ((p : ℝ)*E+1) := by
    filter_upwards [hk.eventually (Ioi_mem_nhds hLower),
      hk.eventually (Iio_mem_nhds hUpper)] with n hn1 hn2
    exact ⟨hn1.le,hn2.le⟩
  have hContactRange : ∀ᶠ n : ℕ in atTop,
      (fun _ : ℕ => (p : ℝ)*E) n ∈
        Icc (2*Real.sqrt b+g) ((p : ℝ)*E+1) :=
    Filter.Eventually.of_forall (fun _ => ⟨hLower.le,hUpper.le⟩)
  have hLogShift := signed_actual_log_mean_agree hb hg k hkRange
  have hLogBase := signed_actual_log_mean_agree hb hg
    (fun _ : ℕ => (p : ℝ)*E) hContactRange
  have hSigned := sourcePure_signedEnergyLogWeight_log_window_tangent p hp a ha h hD σ hσ
  have hTotal := (hLogShift.sub hLogBase).add hSigned
  convert hTotal using 1
  · funext n
    have hBase : (p : ℝ)*((n+2 : ℕ)*E)/(n+2 : ℕ)=(p : ℝ)*E := by
      field_simp
    rw [←pureActualEnergyLogWeight_sub_signed n V b (p : ℝ) ((n+2 : ℕ)*E+σ n),
      ←hBase,←pureActualEnergyLogWeight_sub_signed n V b (p : ℝ) ((n+2 : ℕ)*E)]
    ring
  · ring

/-- The genuine absolute-determinant one-point weight has the source
fixed-shift ratio at any logarithmically centered energy, with a shift of
either sign. -/
theorem sourcePure_actualEnergyLogWeight_fixed_shift
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ))
    (t : ℝ) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    Tendsto (fun n : ℕ =>
      pureActualEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n+t)-
        pureActualEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n))
      atTop (𝓝 (-(β*x)*t)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  have hLog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n+2 : ℕ) := by
    have hh : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    exact hh.eventually (eventually_ge_atTop 1)
  have hσt : ∀ᶠ n : ℕ in atTop,
      |σ n+t| ≤ (D+|t|+1)*Real.log (n+2 : ℕ) := by
    filter_upwards [hσ,hLog] with n hn hlog
    have hh := (abs_add_le (σ n) t).trans (add_le_add_left hn |t|)
    nlinarith [abs_nonneg t]
  have hD' : 0 ≤ D+|t|+1 := by positivity
  have hPlus := sourcePure_actualEnergyLogWeight_log_window_tangent p hp a ha h
    hD' (fun n => σ n+t) hσt
  have hBase := sourcePure_actualEnergyLogWeight_log_window_tangent p hp a ha h
    hD σ hσ
  have hDiff := hPlus.sub hBase
  have hLimit := hDiff.add (tendsto_const_nhds (x := -(β*x)*t))
  convert hLimit using 1
  · funext n
    have hh : (n+2 : ℕ)*E+(σ n+t)=(n+2 : ℕ)*E+σ n+t := by ring
    rw [hh]
    ring
  · ring

end SlowEquilibration.SphericalMarkedWindows
