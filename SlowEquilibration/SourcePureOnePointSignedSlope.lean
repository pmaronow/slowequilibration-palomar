-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GOEPureSignedPhysicalSlopeRate
public import SlowEquilibration.SphericalProperPureContactGeometry
public import SlowEquilibration.NatLogSequenceScales
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Exact finite-dimensional logarithmic energy slope of the proper-pure
signed Kac--Rice weight, before transferring to the ordinary absolute GOE
mean. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set GOEPurePhysicalSignedSlope GOEPureSignedPhysicalSlopeRate
open GOEPhysicalSignedMean GOEScaling GOELogPotential GOEClippedResolvent
open TwoAtomStationarity SphericalTAPCertificate
open Filter
open scoped Topology
set_option maxHeartbeats 500000

def pureSignedEnergyLogWeight (n : ℕ) (V b p H : ℝ) : ℝ :=
  -H^2/(2*(n+2 : ℕ)*V)+
    Real.log (signedPhysicalMean (n+1) (n+2) b (p*H/(n+2 : ℕ)))

/-- The literal Gaussian quadratic and the actual signed physical GOE
characteristic polynomial give this exact physical-energy log derivative. -/
theorem pureSignedEnergyLogWeight_hasDerivAt (n : ℕ) {V b p H : ℝ}
    (hV : 0 < V) (hb : 0 < b)
    (hEdge : 2*Real.sqrt b < p*H/(n+2 : ℕ)) :
    HasDerivAt (pureSignedEnergyLogWeight n V b p)
      (-H/((n+2 : ℕ)*V)+
        p*(n+1 : ℕ)/(n+2 : ℕ)/scaleFactor n (n+2) b*
          jacobiNormalizedResolvent n
            ((p*H/(n+2 : ℕ))/scaleFactor n (n+2) b-2)) H := by
  have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hD : 0 < 2*((n+2 : ℕ):ℝ)*V := by positivity
  have hGaussian : HasDerivAt (fun t : ℝ => -t^2/(2*(n+2 : ℕ)*V))
      (-H/((n+2 : ℕ)*V)) H := by
    convert ((((hasDerivAt_id H).pow 2).neg).div_const (2*(n+2 : ℕ)*V)) using 1
    · funext t; dsimp
    · dsimp; field_simp
  have hArg : HasDerivAt (fun t : ℝ => p*t/(n+2 : ℕ)) (p/(n+2 : ℕ)) H := by
    convert ((hasDerivAt_id H).const_mul p).div_const (n+2 : ℕ) using 1
    funext t
    simp only [id_eq]
    ring
  have hSigned := (signedPhysicalMean_log_hasDerivAt_jacobi n (n+2) (by omega)
    (by omega) hb hEdge).comp H hArg
  convert hGaussian.add hSigned using 1
  · funext t
    rfl
  · push_cast
    ring

/-- The genuine finite GOE/Hermite slope differs from the deterministic
semicircle score by an explicit inverse-dimension error uniformly above a
fixed spectral gap. -/
theorem pureSignedEnergyLogWeight_slope_rate (n : ℕ) {V b p H g : ℝ}
    (hV : 0 < V) (hb : 0 < b) (hp : 0 ≤ p) (hg : 0 < g)
    (hGap : 2*Real.sqrt b+g ≤ p*H/(n+2 : ℕ)) :
    |deriv (pureSignedEnergyLogWeight n V b p) H -
      (-H/((n+2 : ℕ)*V)+p*physicalResolvent b (p*H/(n+2 : ℕ)))| ≤
      (p/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g)/(n+1 : ℕ) := by
  have hEdge : 2*Real.sqrt b < p*H/(n+2 : ℕ) := by linarith
  have hDeriv := (pureSignedEnergyLogWeight_hasDerivAt n hV hb hEdge).deriv
  have hRate := signed_physical_energy_slope_rate n hb hg hp hGap
  rw [hDeriv]
  convert hRate using 1
  · congr 1
    push_cast
    ring
  · push_cast
    ring

/-- At the pure source contact, the exact limiting scalar score of the
signed physical-energy weight is the manuscript's `-βx`. -/
theorem sourcePure_signedEnergy_contact_score
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    (-E/V+(p : ℝ)*physicalResolvent b ((p : ℝ)*E)=-(β*x)) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  have hb : 0 < b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hEdge : 2 < (p : ℝ)*E/Real.sqrt b := by
    apply (lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hs := sourcePure_contact_complexity_derivative p hp a ha h
  change -E/V+(p : ℝ)/Real.sqrt b*
    SemicirclePotential.resolvent ((p : ℝ)*E/Real.sqrt b)=-(β*x) at hs
  change -E/V+(p : ℝ)*physicalResolvent b ((p : ℝ)*E)=-(β*x)
  rw [SemicirclePotential.resolvent_eq_semicircleResolvent hEdge] at hs
  unfold physicalResolvent
  convert hs using 1; ring

/-- The exact signed Kac--Rice physical-energy log slope approaches the
pure source slope uniformly along every fixed-size logarithmic perturbation
of contact. The pointwise sequence can vary arbitrarily inside that band. -/
theorem sourcePure_signedEnergyLogSlope_log_window_tendsto
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ)) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    Tendsto (fun n : ℕ => deriv (pureSignedEnergyLogWeight n V b (p : ℝ))
      ((n+2 : ℕ)*E+σ n)) atTop (𝓝 (-(β*x))) := by
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  let g := ((p : ℝ)*E-2*Real.sqrt b)/2
  let k : ℕ → ℝ := fun n => (p : ℝ)*(E+σ n/(n+2 : ℕ))
  have hV : 0 < V := μ.xi_pos h.overlap_range.1
  have hb : 0 < b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hpPos : 0 ≤ (p : ℝ) := by positivity
  have hGap : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hg : 0 < g := by dsimp [g]; linarith
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hE : Tendsto (fun n : ℕ => E+σ n/(n+2 : ℕ)) atTop (𝓝 E) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := E)).add hσzero
  have hk : Tendsto k atTop (𝓝 ((p : ℝ)*E)) := by
    simpa only [k] using hE.const_mul (p : ℝ)
  have hkGap : ∀ᶠ n : ℕ in atTop, 2*Real.sqrt b+g ≤ k n := by
    have hStrict : 2*Real.sqrt b+g < (p : ℝ)*E := by dsimp [g]; linarith
    exact (hk.eventually (Ioi_mem_nhds hStrict)).mono (fun _ hn => hn.le)
  have hNexpr (n : ℕ) :
      (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ)=k n := by
    dsimp [k]
    have hN : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hScoreT : Tendsto (fun n : ℕ =>
      -((n+2 : ℕ)*E+σ n)/((n+2 : ℕ)*V)+
        (p : ℝ)*physicalResolvent b (k n)) atTop (𝓝 (-(β*x))) := by
    have hRes := (physicalResolvent_continuous_shift b).continuousAt.tendsto.comp hk
    have hBase := hE.neg.div_const V
    have hSum := hBase.add (hRes.const_mul (p : ℝ))
    have hContact := sourcePure_signedEnergy_contact_score p hp a ha h
    change -E/V+(p : ℝ)*physicalResolvent b ((p : ℝ)*E)=-(β*x) at hContact
    rw [hContact] at hSum
    convert hSum using 1
    funext n
    have hN : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    field_simp
  let K := ((p : ℝ)/b)*(Real.sqrt b/(g/Real.sqrt b)^3+2*b/g)
  have hRate : ∀ᶠ n : ℕ in atTop,
      |deriv (pureSignedEnergyLogWeight n V b (p : ℝ)) ((n+2 : ℕ)*E+σ n)-
        (-((n+2 : ℕ)*E+σ n)/((n+2 : ℕ)*V)+
          (p : ℝ)*physicalResolvent b (k n))| ≤ K/(n+1 : ℕ) := by
    filter_upwards [hkGap] with n hn
    have hn' : 2*Real.sqrt b+g ≤
        (p : ℝ)*((n+2 : ℕ)*E+σ n)/(n+2 : ℕ) := by rw [hNexpr]; exact hn
    have hh := pureSignedEnergyLogWeight_slope_rate n hV hb hpPos hg hn'
    rw [hNexpr] at hh
    exact hh
  have hDim : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hKzero : Tendsto (fun n : ℕ => K/(n+1 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
    hDim.const_div_atTop K
  have hErr : Tendsto (fun n : ℕ =>
      deriv (pureSignedEnergyLogWeight n V b (p : ℝ)) ((n+2 : ℕ)*E+σ n)-
        (-((n+2 : ℕ)*E+σ n)/((n+2 : ℕ)*V)+
          (p : ℝ)*physicalResolvent b (k n))) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm' _ hKzero
    filter_upwards [hRate] with n hn
    simpa only [Real.norm_eq_abs] using hn
  have hSum := hErr.add hScoreT
  simpa only [zero_add,sub_add_cancel] using hSum

/-- Every positive fixed physical-energy shift has the source signed
logarithmic intensity ratio along an arbitrary logarithmic center sequence. -/
theorem sourcePure_signedEnergyLogWeight_positive_fixed_shift
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop, |σ n| ≤ D*Real.log (n+2 : ℕ))
    {t : ℝ} (ht : 0 < t) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let V := μ.xi Q
    let b := Q^2*μ.xi2 Q
    Tendsto (fun n : ℕ =>
      pureSignedEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n+t)-
        pureSignedEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n))
      atTop (𝓝 (-(β*x)*t)) := by
  classical
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let V := μ.xi Q
  let b := Q^2*μ.xi2 Q
  let m : ℕ → ℝ := fun n => (n+2 : ℕ)*E+σ n
  let f : ℕ → ℝ → ℝ := fun n => pureSignedEnergyLogWeight n V b (p : ℝ)
  have hV : 0 < V := μ.xi_pos h.overlap_range.1
  have hb : 0 < b := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hpPos : 0 ≤ (p : ℝ) := by positivity
  have hContact : 2*Real.sqrt b < (p : ℝ)*E := by
    rw [←sourcePure_contact_radial_graph p hp a ha h]
    exact sourceContact_markK_above_edge μ h
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hK : Tendsto (fun n : ℕ => (p : ℝ)*(m n)/(n+2 : ℕ)) atTop
      (𝓝 ((p : ℝ)*E)) := by
    have hh := ((tendsto_const_nhds (x := E)).add hσzero).const_mul (p : ℝ)
    convert hh using 1
    · funext n
      dsimp [m]
      have hN : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    · ring
  have hEdge : ∀ᶠ n : ℕ in atTop, 2*Real.sqrt b < (p : ℝ)*m n/(n+2 : ℕ) :=
    hK.eventually (Ioi_mem_nhds hContact)
  have hMVT : ∀ᶠ n : ℕ in atTop,
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ t ∧
        f n (m n+t)-f n (m n)=t*deriv (f n) (m n+v) := by
    filter_upwards [hEdge] with n hn
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hAt (H : ℝ) (hH : m n ≤ H) :
        2*Real.sqrt b < (p : ℝ)*H/(n+2 : ℕ) := by
      have hm := mul_le_mul_of_nonneg_left hH hpPos
      have hDiv := div_le_div_of_nonneg_right hm hN.le
      linarith
    have hCont : ContinuousOn (f n) (Icc (m n) (m n+t)) := by
      intro H hH
      exact (pureSignedEnergyLogWeight_hasDerivAt n hV hb (hAt H hH.1)).continuousAt.continuousWithinAt
    have hDiff : DifferentiableOn ℝ (f n) (Ioo (m n) (m n+t)) := by
      intro H hH
      exact (pureSignedEnergyLogWeight_hasDerivAt n hV hb (hAt H hH.1.le)).differentiableAt.differentiableWithinAt
    obtain ⟨c,hc,hSlope⟩ := exists_deriv_eq_slope (f n)
      (by linarith : m n < m n+t) hCont hDiff
    refine ⟨c-m n,by linarith [hc.1],by linarith [hc.2],?_⟩
    have hDen : (m n+t)-m n=t := by ring
    rw [hDen] at hSlope
    have hMul := (eq_div_iff ht.ne').mp hSlope
    have hcEq : m n+(c-m n)=c := by ring
    rw [hcEq]
    nlinarith [hMul]
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hMVT
  let v : ℕ → ℝ := fun n => if hn : n₀ ≤ n then Classical.choose (hn₀ n hn) else 0
  have hv : ∀ᶠ n : ℕ in atTop,
      0 ≤ v n ∧ v n ≤ t ∧ f n (m n+t)-f n (m n)=t*deriv (f n) (m n+v n) := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    simpa only [v,dite_eq_left hn] using Classical.choose_spec (hn₀ n hn)
  have hLog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n+2 : ℕ) := by
    have hh : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    exact hh.eventually (eventually_ge_atTop 1)
  have hσv : ∀ᶠ n : ℕ in atTop,
      |σ n+v n| ≤ (D+t+1)*Real.log (n+2 : ℕ) := by
    filter_upwards [hσ,hv,hLog] with n hn hvn hlog
    have hAbs := (abs_add_le (σ n) (v n)).trans
      (add_le_add_left hn |v n|)
    have hvAbs : |v n| ≤ t := by rw [abs_of_nonneg hvn.1]; exact hvn.2.1
    nlinarith
  have hD' : 0 ≤ D+t+1 := by linarith
  have hSlope := sourcePure_signedEnergyLogSlope_log_window_tendsto p hp a ha h hD'
    (fun n => σ n+v n) hσv
  have hSlope' : Tendsto (fun n : ℕ => deriv (f n) (m n+v n)) atTop (𝓝 (-(β*x))) := by
    convert hSlope using 1
    funext n
    dsimp [f,m]
    congr 1
    ring
  have hLimit := hSlope'.const_mul t
  have heq : (fun n : ℕ => f n (m n+t)-f n (m n)) =ᶠ[atTop]
      (fun n : ℕ => t*deriv (f n) (m n+v n)) :=
    hv.mono (fun _ hn => hn.2.2)
  have hLimit' := hLimit.congr' heq.symm
  simpa only [f,m,show t*(-(β*x))=-(β*x)*t by ring] using hLimit'

/-- The signed physical-energy log ratio at the pure source contact for any
fixed displacement, including negative displacements. -/
theorem sourcePure_signedEnergyLogWeight_fixed_shift
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
      pureSignedEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n+t)-
        pureSignedEnergyLogWeight n V b (p : ℝ) ((n+2 : ℕ)*E+σ n))
      atTop (𝓝 (-(β*x)*t)) := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hLog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n+2 : ℕ) := by
      have hh : Tendsto (fun n : ℕ => Real.log (n+2 : ℕ)) atTop atTop :=
        Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
      exact hh.eventually (eventually_ge_atTop 1)
    have hShift : ∀ᶠ n : ℕ in atTop,
        |σ n+t| ≤ (D+|t|+1)*Real.log (n+2 : ℕ) := by
      filter_upwards [hσ,hLog] with n hn hlog
      have hAbs := (abs_add_le (σ n) t).trans (add_le_add_left hn |t|)
      nlinarith [abs_nonneg t]
    have hD' : 0 ≤ D+|t|+1 := by positivity
    have hPos := sourcePure_signedEnergyLogWeight_positive_fixed_shift p hp a ha h
      hD' (fun n => σ n+t) hShift (show 0 < -t by linarith)
    have hNeg := hPos.neg
    convert hNeg using 1
    · funext n
      have harg : ((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q+
          (σ n+t))+(-t)=(n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q+σ n := by ring
      simp only [harg]
      ring
    · ring
  · subst t
    simpa only [add_zero,sub_self,mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · exact sourcePure_signedEnergyLogWeight_positive_fixed_shift p hp a ha h hD σ hσ ht

end SlowEquilibration.SphericalMarkedWindows
