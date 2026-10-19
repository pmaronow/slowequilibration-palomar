module
public import FourPapersCommon.SignedBouDupuis
public import FourPapersCommon.ScalarControlCombination
public import QuantitativeFollowup.ChenControlAlgebra

@[expose] public section

/-! Scalar Gaussian smoothing preserves joint convexity in the moment parameter
and the remaining coordinates. The proof uses the genuine signed Brownian
control representation, not an assumed Gaussian convexity theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon Paper ColeHopfFoundation.ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

def signedGaussianStep (F : ℝ × E × ℝ → ℝ) (p : ℝ × E) : ℝ :=
  coleHopf p.1 1 (fun y=>F (p.1,p.2,y)) 0

theorem convexOn_signedGaussianStep_positive (F : ℝ × E × ℝ → ℝ)
    (hF : ConvexOn ℝ ((Ioi (0:ℝ)) ×ˢ (univ : Set (E × ℝ))) F)
    (hreg : ∀ m z,SignedScalarDatum (fun y=>F (m,z,y))) :
    ConvexOn ℝ ((Ioi (0:ℝ)) ×ˢ (univ : Set E)) (signedGaussianStep F) := by
  refine ⟨(convex_Ioi 0).prod convex_univ,?_⟩
  rintro ⟨m0,z0⟩ hp0 ⟨m1,z1⟩ hp1 a b ha hb hab
  have h0 : 0 < m0 := hp0.1
  have h1 : 0 < m1 := hp1.1
  have hm : 0 < a*m0+b*m1 := by
    have hh := (convex_Ioi (0:ℝ)) h0 h1 ha hb hab
    simpa only [smul_eq_mul,Set.mem_Ioi,Set.mem_Iio] using hh
  let m := a*m0+b*m1
  let z := a • z0+b • z1
  obtain ⟨A,hA,hoptimal⟩ := exists_scalarBrownianPayoff_eq_heat (hreg m z) m 0 hm.ne'
  have hineq (sample : BrownianSample) :
      F (m,z,scalarControlledState m 0 A 1 sample) ≤
        a*F (m0,z0,scalarControlledState m0 0 A 1 sample)+
        b*F (m1,z1,scalarControlledState m1 0 A 1 sample) := by
    have hh := hF.2 (show (m0,z0,scalarControlledState m0 0 A 1 sample) ∈
      (Ioi (0:ℝ)) ×ˢ (univ : Set (E × ℝ)) from ⟨h0,mem_univ _⟩)
      (show (m1,z1,scalarControlledState m1 0 A 1 sample) ∈
        (Ioi (0:ℝ)) ×ˢ (univ : Set (E × ℝ)) from ⟨h1,mem_univ _⟩) ha hb hab
    have he := scalarControlledState_terminal_sameControl m0 m1 0 0 a b hab A sample
    simp only [mul_zero,add_zero] at he
    change F (a*m0+b*m1,a • z0+b • z1,
      a*scalarControlledState m0 0 A 1 sample+b*scalarControlledState m1 0 A 1 sample) ≤ _ at hh
    rw [←he] at hh
    exact hh
  obtain ⟨L,hL⟩ := (hreg m z).lipschitz
  obtain ⟨L0,hL0⟩ := (hreg m0 z0).lipschitz
  obtain ⟨L1,hL1⟩ := (hreg m1 z1).lipschitz
  have hi := integrable_lipschitz_scalarControlledState m 0 A hA 1 _ L hL
  have hi0 := integrable_lipschitz_scalarControlledState m0 0 A hA 1 _ L0 hL0
  have hi1 := integrable_lipschitz_scalarControlledState m1 0 A hA 1 _ L1 hL1
  have hh := integral_mono hi ((hi0.const_mul a).add (hi1.const_mul b)) hineq
  have hadd := integral_add (hi0.const_mul a) (hi1.const_mul b)
  try simp only [Pi.add_apply] at hadd
  simp only [Pi.add_apply] at hh
  rw [hadd,integral_const_mul,integral_const_mul] at hh
  have hpay : scalarBrownianPayoff (fun y=>F (m,z,y)) m 0 A ≤
      a*scalarBrownianPayoff (fun y=>F (m0,z0,y)) m0 0 A+
      b*scalarBrownianPayoff (fun y=>F (m1,z1,y)) m1 0 A := by
    unfold scalarBrownianPayoff
    dsimp [m] at hh ⊢
    linear_combination hh
  have hpay0 := scalarBrownianPayoff_le_heat_of_pos (hreg m0 z0) m0 0 h0 A hA
  have hpay1 := scalarBrownianPayoff_le_heat_of_pos (hreg m1 z1) m1 0 h1 A hA
  have hbound := hpay.trans (add_le_add (mul_le_mul_of_nonneg_left hpay0 ha)
    (mul_le_mul_of_nonneg_left hpay1 hb))
  rw [hoptimal] at hbound
  rw [signedHeatLog_exp_eq_coleHopf (fun y=>F (m,z,y)) m 1 0 (show m ≠ 0 from hm.ne'),
    signedHeatLog_exp_eq_coleHopf (fun y=>F (m0,z0,y)) m0 1 0 h0.ne',
    signedHeatLog_exp_eq_coleHopf (fun y=>F (m1,z1,y)) m1 1 0 h1.ne'] at hbound
  convert! hbound using 1 <;> simp [signedGaussianStep,m,z]


theorem chen_negative_expected_control_energy (m0 m1 a b : ℝ)
    (h0 : m0 < 0) (h1 : m1 < 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (A0 A1 : ℝ → BrownianSample → ℝ) (hA0 : IsScalarBrownianControl A0)
    (hA1 : IsScalarBrownianControl A1) :
    -(a*m0+b*m1)*(∫ sample,(∫ s in 0..(1:ℝ),
      (a*m0/(a*m0+b*m1)*A0 s sample+b*m1/(a*m0+b*m1)*A1 s sample)^2)
      ∂canonicalBrownianMeasure) ≤
      -(a*m0)*(∫ sample,(∫ s in 0..(1:ℝ),A0 s sample^2) ∂canonicalBrownianMeasure)-
      (b*m1)*(∫ sample,(∫ s in 0..(1:ℝ),A1 s sample^2) ∂canonicalBrownianMeasure) := by
  let m := a*m0+b*m1
  let A := fun s sample=>a*m0/m*A0 s sample+b*m1/m*A1 s sample
  have hA := hA0.linearCombination hA1 (a*m0/m) (b*m1/m)
  have hpoint (s : ℝ) (sample : BrownianSample) :
      -m*A s sample^2 ≤ -(a*m0)*A0 s sample^2-(b*m1)*A1 s sample^2 := by
    have hh := chen_negative_energy_mix a b m0 m1 (A0 s sample) (A1 s sample) ha hb hab h0 h1
    simpa only [chenNegativeControlMix,smul_eq_mul,Real.norm_eq_abs,sq_abs,m,A] using hh
  have htime (sample : BrownianSample) :
      -m*(∫ s in 0..(1:ℝ),A s sample^2) ≤
        -(a*m0)*(∫ s in 0..(1:ℝ),A0 s sample^2)-
        (b*m1)*(∫ s in 0..(1:ℝ),A1 s sample^2) := by
    have hl : IntervalIntegrable (fun s=>-m*A s sample^2) volume 0 1 :=
      (continuous_const.mul ((hA.continuous_paths sample).pow 2)).intervalIntegrable 0 1
    have hr0 : IntervalIntegrable (fun s=>-(a*m0)*A0 s sample^2) volume 0 1 :=
      (continuous_const.mul ((hA0.continuous_paths sample).pow 2)).intervalIntegrable 0 1
    have hr1 : IntervalIntegrable (fun s=>(b*m1)*A1 s sample^2) volume 0 1 :=
      (continuous_const.mul ((hA1.continuous_paths sample).pow 2)).intervalIntegrable 0 1
    have hh := intervalIntegral.integral_mono (by norm_num : (0:ℝ) ≤ 1) hl (hr0.sub hr1)
      (fun s=>hpoint s sample)
    have hsub := intervalIntegral.integral_sub hr0 hr1
    try simp only [Pi.sub_apply] at hsub
    rw [hsub] at hh
    simpa only [intervalIntegral.integral_const_mul] using hh
  have hi := integrable_scalarControlEnergy A hA
  have hi0 := integrable_scalarControlEnergy A0 hA0
  have hi1 := integrable_scalarControlEnergy A1 hA1
  have hh := integral_mono (hi.const_mul (-m))
    ((hi0.const_mul (-(a*m0))).sub (hi1.const_mul (b*m1))) htime
  have hsub := integral_sub (hi0.const_mul (-(a*m0))) (hi1.const_mul (b*m1))
  try simp only [Pi.sub_apply] at hsub
  simp only [Pi.sub_apply] at hh
  rw [hsub] at hh
  simpa only [integral_const_mul,m,A] using hh

theorem convexOn_signedGaussianStep_negative (F : ℝ × E × ℝ → ℝ)
    (hF : ConvexOn ℝ ((Iio (0:ℝ)) ×ˢ (univ : Set (E × ℝ))) F)
    (hreg : ∀ m z,SignedScalarDatum (fun y=>F (m,z,y))) :
    ConvexOn ℝ ((Iio (0:ℝ)) ×ˢ (univ : Set E)) (signedGaussianStep F) := by
  refine ⟨(convex_Iio 0).prod convex_univ,?_⟩
  rintro ⟨m0,z0⟩ hp0 ⟨m1,z1⟩ hp1 a b ha hb hab
  have h0 : m0 < 0 := hp0.1
  have h1 : m1 < 0 := hp1.1
  have hm : a*m0+b*m1 < 0 := by
    have hh := (convex_Iio (0:ℝ)) h0 h1 ha hb hab
    simpa only [smul_eq_mul,Set.mem_Ioi,Set.mem_Iio] using hh
  let m := a*m0+b*m1
  let z := a • z0+b • z1
  obtain ⟨A0,hA0,hoptimal0⟩ := exists_scalarBrownianPayoff_eq_heat (hreg m0 z0) m0 0 h0.ne
  obtain ⟨A1,hA1,hoptimal1⟩ := exists_scalarBrownianPayoff_eq_heat (hreg m1 z1) m1 0 h1.ne
  let A := fun s sample=>a*m0/m*A0 s sample+b*m1/m*A1 s sample
  have hA := hA0.linearCombination hA1 (a*m0/m) (b*m1/m)
  have hc0 : m*(a*m0/m)=a*m0 := by field_simp [show m ≠ 0 from hm.ne]
  have hc1 : m*(b*m1/m)=b*m1 := by field_simp [show m ≠ 0 from hm.ne]
  have hineq (sample : BrownianSample) :
      F (m,z,scalarControlledState m 0 A 1 sample) ≤
        a*F (m0,z0,scalarControlledState m0 0 A0 1 sample)+
        b*F (m1,z1,scalarControlledState m1 0 A1 1 sample) := by
    have hh := hF.2 (show (m0,z0,scalarControlledState m0 0 A0 1 sample) ∈
      (Iio (0:ℝ)) ×ˢ (univ : Set (E × ℝ)) from ⟨h0,mem_univ _⟩)
      (show (m1,z1,scalarControlledState m1 0 A1 1 sample) ∈
        (Iio (0:ℝ)) ×ˢ (univ : Set (E × ℝ)) from ⟨h1,mem_univ _⟩) ha hb hab
    have he := scalarControlledState_terminal_linearCombination m m0 m1 0 0 a b
      (a*m0/m) (b*m1/m) hab hc0 hc1 A0 A1 hA0 hA1 sample
    simp only [mul_zero,add_zero] at he
    change F (a*m0+b*m1,a • z0+b • z1,
      a*scalarControlledState m0 0 A0 1 sample+b*scalarControlledState m1 0 A1 1 sample) ≤ _ at hh
    rw [←he] at hh
    exact hh
  obtain ⟨L,hL⟩ := (hreg m z).lipschitz
  obtain ⟨L0,hL0⟩ := (hreg m0 z0).lipschitz
  obtain ⟨L1,hL1⟩ := (hreg m1 z1).lipschitz
  have hi := integrable_lipschitz_scalarControlledState m 0 A hA 1 _ L hL
  have hi0 := integrable_lipschitz_scalarControlledState m0 0 A0 hA0 1 _ L0 hL0
  have hi1 := integrable_lipschitz_scalarControlledState m1 0 A1 hA1 1 _ L1 hL1
  have hh := integral_mono hi ((hi0.const_mul a).add (hi1.const_mul b)) hineq
  have hadd := integral_add (hi0.const_mul a) (hi1.const_mul b)
  try simp only [Pi.add_apply] at hadd
  simp only [Pi.add_apply] at hh
  rw [hadd,integral_const_mul,integral_const_mul] at hh
  have henergy := chen_negative_expected_control_energy m0 m1 a b h0 h1 ha hb hab A0 A1 hA0 hA1
  have hpay : scalarBrownianPayoff (fun y=>F (m,z,y)) m 0 A ≤
      a*scalarBrownianPayoff (fun y=>F (m0,z0,y)) m0 0 A0+
      b*scalarBrownianPayoff (fun y=>F (m1,z1,y)) m1 0 A1 := by
    unfold scalarBrownianPayoff
    change -m*(∫ sample,(∫ s in 0..(1:ℝ),A s sample^2) ∂canonicalBrownianMeasure) ≤
      -(a*m0)*(∫ sample,(∫ s in 0..(1:ℝ),A0 s sample^2) ∂canonicalBrownianMeasure)-
      (b*m1)*(∫ sample,(∫ s in 0..(1:ℝ),A1 s sample^2) ∂canonicalBrownianMeasure) at henergy
    linear_combination hh+(1/2)*henergy
  have hbound := (heat_le_scalarBrownianPayoff_of_neg (hreg m z) m 0 hm A hA).trans hpay
  rw [hoptimal0,hoptimal1] at hbound
  rw [signedHeatLog_exp_eq_coleHopf (fun y=>F (m,z,y)) m 1 0 (show m ≠ 0 from hm.ne),
    signedHeatLog_exp_eq_coleHopf (fun y=>F (m0,z0,y)) m0 1 0 h0.ne,
    signedHeatLog_exp_eq_coleHopf (fun y=>F (m1,z1,y)) m1 1 0 h1.ne] at hbound
  convert! hbound using 1 <;> simp [signedGaussianStep,m,z]

end QuantitativeFollowup
