-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapAngularErrorIntegral
public import SlowEquilibration.SourcePureOriginalEdgeMargin
public import SlowEquilibration.SphericalPureDenominatorScaleLimit
public import SlowEquilibration.SourcePureAboveStaticCertificate

/-! The source pure capture estimates with a single cap fixed before every
energy window, microscopic width, dimension, and denominator threshold.
The quantities below are literal all-critical partition sums for the original
amplitude-one Hamiltonian.  All analytic and marked Kac--Rice inputs are proved;
there is no coarse-cover hypothesis in this packet. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCaptureFixedCapEstimates
noncomputable section
open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCertificate PureStationarity
open SourcePureCapBorelMarkedValue SourcePureCapDeepEnergyIntegral
open SourcePureCapAngularErrorIntegral SourcePureOriginalEdgeMargin
open SphericalPureCapSourceScalars SphericalPureCapSourceRatios
open SphericalPureCapSourceRatiosFixed SphericalPureDenominatorScaleLimit
open SphericalPureCapTailScale SourceGaussianWindowFraction
open SourceGaussianLaplaceRatio
open SphericalKacRiceGluing
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The manuscript's physical critical-energy center in dimension `d+2`. -/
def pureSourceCenter (p : ℕ) (hp : 4 ≤ p) (d : ℕ) : ℝ :=
  (d+2:ℕ)*pureEnergyConstant p (by omega)-
    Real.log (d+2:ℕ)/(2*pureIntensityConstant p (by omega))

/-- The exact deterministic cap normalizer `𝒜_N`.  Its identification with
the original value-conditioned mean is `sourceCapMean_eq_original_conditioned`. -/
def pureSourceCapMean (p : ℕ) (hp : 4 ≤ p) (β a : ℝ) (d : ℕ) : ℝ :=
  sourceCapMean p β (pureEnergyConstant p (by omega))
    (pureIntensityConstant p (by omega)) a d 0

/-- Original-disorder expectation of all critical cap partitions below the
fixed window, including the moving coarse-cover lower endpoint. -/
def pureSourceDeepSum (p : ℕ) (hp : 4 ≤ p) (β a : ℝ)
    (d : ℕ) (l L : ℝ) : ℝ≥0∞ :=
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  ∫⁻ J, actualScoreWindowCount (d+1)
    (centerCoefficients (mixtureCoefficients μ) 1)
    (physicalEnergyWindow (d+2) (Icc l (pureSourceCenter p hp d-L)) univ)
    (originalBorelBandMark d μ β (Ico a 1)) J
    ∂disorderLaw (d+2) μ.maxDegree

/-- Original-disorder expectation of the disconnected cap outside each
microscopic window, summed over all critical points of the fixed energy window. -/
def pureSourceAngularSum (p : ℕ) (hp : 4 ≤ p) (β Q a : ℝ)
    (d : ℕ) (L w : ℝ) : ℝ≥0∞ :=
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  ∫⁻ J, actualScoreWindowCount (d+1)
    (centerCoefficients (mixtureCoefficients μ) 1)
    (physicalEnergyWindow (d+2)
      (Icc (pureSourceCenter p hp d-L) (pureSourceCenter p hp d+L)) univ)
    (originalBorelBandMark d μ β
      (Ico a 1 \ Icc (Real.sqrt Q-w/Real.sqrt (d+2:ℕ))
        (Real.sqrt Q+w/Real.sqrt (d+2:ℕ)))) J
    ∂disorderLaw (d+2) μ.maxDegree

/-- The denominator failure probability at the same cap scale and dimension
as both marked sums. -/
def pureSourceDenominatorFailure (p : ℕ) (hp : 4 ≤ p) (β a η : ℝ)
    (n : ℕ) : ℝ :=
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  (disorderLaw (n+2) μ.maxDegree).real
    {J | partition (n+2) β (field (mixtureCoefficients μ) J) <
      η*pureSourceCapMean p hp β a n}

/-- The substantive analytic inputs to the final pure microscopic-capture
argument, with all quantifiers in source order. -/
structure FixedCapEstimates (p : ℕ) (hp : 4 ≤ p)
    (β Q a κ δ : ℝ) : Prop where
  cap_positive : 0 < a
  cap_below_overlap : a < Real.sqrt Q
  cap_below_one : a < 1
  curvature_positive : 0 < κ
  curvature_eq : κ = SphericalPureLaplaceUniformLogCurvature.purePrintedKStar p hp β Q
  deficit_positive : 0 < δ
  residual_subcritical : pureResidualCoefficient p β a < 1/2
  depth_rate_positive : pureIntensityConstant p (by omega) < β*a^p
  mean_nonnegative : ∀ d : ℕ, 0 ≤ pureSourceCapMean p hp β a d
  mean_eventually_positive : ∀ᶠ d : ℕ in atTop, 0 < pureSourceCapMean p hp β a d
  deep : ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
    ∀ L : ℝ, 0 ≤ L → ∀ l : ℝ,
      (d+2:ℕ)*(pureEnergyConstant p (by omega)-δ) ≤ l →
      pureSourceDeepSum p hp β a d l L ≤
        ENNReal.ofReal (C*pureSourceCapMean p hp β a d*
          Real.exp (-(β*a^p-pureIntensityConstant p (by omega))*L))
  angular : ∀ L : ℝ, 0 < L → ∃ C : ℝ, 0 < C ∧
    ∀ w : ℝ, 0 < w → ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
      pureSourceAngularSum p hp β Q a d L w ≤
        ENNReal.ofReal (C*pureSourceCapMean p hp β a d*
          (1-gaussianWindowFraction κ w+ε))
  denominator : Tendsto
    (fun η : ℝ => Filter.limsup (pureSourceDenominatorFailure p hp β a η) atTop)
    (𝓝[>] (0:ℝ)) (𝓝 0)

/-- Original pure `pc-deep`, `pc-angular`, and `pc-denominator` at one
selected cap.  The only physical premise is the actual pure TAP certificate;
the exterior energy box and every marked-sum estimate are constructed. -/
theorem pure_original_capture_fixed_cap_estimates
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    ∃ a κ δ : ℝ, FixedCapEstimates p hp β Q a κ δ := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let F := CSParisiMeasure.variationalValue μ β
  obtain ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,hScale,hRatios⟩ :=
    sourcePure_cap_gaussian_ratios_fixed p hp h
  have ha0 : 0 < a := lt_trans (by positivity : (0:ℝ)<1/Real.sqrt 2) ha
  have haq : a < Real.sqrt Q := by linarith
  have ha1 : a < 1 := by linarith
  let edge := 2*Real.sqrt (μ.xi2 1)
  have hgap : edge < (p:ℝ)*ep := by
    have hh := source_pure_original_ground_energy_above_edge p hp h
    simpa only [edge,μ,ep,pure_xi2,one_pow,mul_one] using hh
  have hp0 : 0 < (p:ℝ) := by positivity
  let δ := ((p:ℝ)*ep-edge)/(4*(p:ℝ))
  let g := ((p:ℝ)*ep-edge)/2
  let Z := (p:ℝ)*(ep+δ)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by positivity)
  have hg : 0 < g := half_pos (sub_pos.mpr hgap)
  have hδmul : (p:ℝ)*δ=((p:ℝ)*ep-edge)/4 := by
    dsimp [δ]
    field_simp [ne_of_gt hp0]
  have hLeft : edge+g ≤ (p:ℝ)*(ep-δ) := by
    dsimp only [g]
    nlinarith [hδmul]
  let u (d : ℕ) : Vector (d+2) := southPole (d+1)
  have hu (d : ℕ) : ‖u d‖^2=(d+2:ℕ) := by
    simpa only [u,Nat.add_assoc,Nat.reduceAdd] using southPole_norm_sq (d+1)
  have hDeep := pure_original_deep_energy_cap_sum p hp h ⟨ha0,ha1⟩
    hres hdepth hδ hg hLeft (le_refl Z) u hu
  have hMeanPos : ∀ᶠ d : ℕ in atTop, 0 < pureSourceCapMean p hp β a d := by
    obtain ⟨hFull,_,hOutside⟩ := hRatios 0 (by norm_num) 1 (by norm_num)
    have hh := source_cap_outside_mean_eventually_le p β ep cp a (Real.sqrt Q)
      κ 0 1 h.beta_pos.le ⟨ha0.le,ha1.le⟩ (by norm_num) hκ hFull hOutside
      (Real.sqrt_nonneg Q) 1 (by norm_num)
    exact hh.mono fun d hd => hd.1
  refine ⟨a,κ,δ,{
    cap_positive := ha0
    cap_below_overlap := haq
    cap_below_one := ha1
    curvature_positive := hκ
    curvature_eq := hκEq
    deficit_positive := hδ
    residual_subcritical := hres
    depth_rate_positive := hdepth
    mean_nonnegative := fun d => source_cap_mean_nonneg p d β ep cp a 0 ha0.le ha1.le
    mean_eventually_positive := hMeanPos
    deep := ?_
    angular := ?_
    denominator := ?_ }⟩
  · simpa only [pureSourceDeepSum,pureSourceCenter,pureSourceCapMean,ep,cp,μ]
      using hDeep
  · intro L hL
    have hAngular := pure_original_angular_error_cap_sum p hp h ⟨ha0,ha1⟩
      haq hres hδ hg hκ hLeft (le_refl Z) u hu L hL
      (fun w hw => ⟨(hRatios L hL.le w hw).1,(hRatios L hL.le w hw).2.2⟩)
    simpa only [pureSourceAngularSum,pureSourceCenter,pureSourceCapMean,ep,cp,μ]
      using hAngular
  · let A (n : ℕ) := sourceCapMean p β ep cp a (n+1) 0
    let K := ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi))*
      Real.sqrt (Real.pi/(κ/2))
    have hzero : (0:ℝ) ∈ Icc (-(0:ℝ)) 0 := by simp
    have hLimit := (hScale 0 (by norm_num)).tendsto_at hzero
    have hA : Tendsto (fun n : ℕ => capScale (n+3) F (1/(2*x))*A n)
        atTop (𝓝 K) := by
      have hh := hLimit.comp (tendsto_add_atTop_nat 1)
      simpa only [A,K,F,μ,ep,cp,Function.comp_def,Nat.add_assoc,Nat.reduceAdd,
        mul_zero,zero_mul,Real.exp_zero,mul_one] using hh
    have hAnonneg (n : ℕ) : 0 ≤ A n :=
      source_cap_mean_nonneg p (n+1) β ep cp a 0 ha0.le ha1.le
    have hDen := pure_partition_cap_scale_denominator_limit p hp h A hAnonneg K hA
    have hShift (η : ℝ) :
        Filter.limsup (fun n => pureSourceDenominatorFailure p hp β a η (n+1)) atTop =
          Filter.limsup (pureSourceDenominatorFailure p hp β a η) atTop := by
      rw [← Function.comp_def,limsup_comp,map_add_atTop_eq_nat]
    have hDen' : Tendsto
        (fun η : ℝ => Filter.limsup
          (fun n => pureSourceDenominatorFailure p hp β a η (n+1)) atTop)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [pureSourceDenominatorFailure,pureSourceCapMean,A,ep,cp,μ,
        Nat.add_assoc,Nat.reduceAdd] using hDen
    simpa only [hShift] using hDen'

/-- The same literal deep, angular, and denominator estimates throughout
the manuscript's full superstatic pure regime. -/
theorem pure_original_capture_fixed_cap_estimates_above_static
    (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x Q a κ δ : ℝ,
      Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q ∧
      FixedCapEstimates p hp β Q a κ δ := by
  obtain ⟨x,Q,h⟩ := pure_certificate_above_static p hp hβ
  obtain ⟨a,κ,δ,hEst⟩ := pure_original_capture_fixed_cap_estimates p hp h
  exact ⟨x,Q,a,κ,δ,h,hEst⟩

end
end SlowEquilibration.SourcePureCaptureFixedCapEstimates
