-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetBankSecondMoment
public import SlowEquilibration.SphericalQuadraticLatitudeJetPureBankFubini

@[expose] public section

/-! The genuine quadratic Taylor bank under the proper-pure posterior
has the exact two-replica second moment and a uniform overlap bound. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalTAPCriticalAnalyticNeighborhood
open ConditionedDeterminantMoments SphericalMarkedWindows
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

theorem quadraticBankPoint_prod_integrable_pure
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) :
    Integrable (fun w : Disorder (d+2) μ.maxDegree × Vector (d+1) =>
      quadraticBankPoint μ a β u w.1 w.2)
      ((valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).prod (sphereLaw (d+1))) := by
  haveI : IsProbabilityMeasure (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
    unfold valueConditionedLaw
    infer_instance
  let m := Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2)
  have hm := quadraticBankPoint_joint_measurable μ a β u
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun y => quadraticBankPoint_physicalPurePalm_integrable
    μ hμ Q a β u hu b y),?_⟩
  apply (integrable_const m).congr
  filter_upwards [sphereLaw_support (by omega : 1≤d+1)] with y hy
  have hh := quadraticBankPoint_physicalPurePalm_mean
    μ hμ Q a β u hu b y hy
  have hnorm : (fun J : Disorder (d+2) μ.maxDegree =>
      ‖quadraticBankPoint μ a β u J y‖) =
      (fun J => quadraticBankPoint μ a β u J y) := by
    funext J
    unfold quadraticBankPoint
    simp
  rw [hnorm]
  exact hh.symm

theorem quadraticBankPartition_physicalPurePalm_integrable
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) :
    Integrable (quadraticBankPartition μ a β u)
      (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
  convert (quadraticBankPoint_prod_integrable_pure μ hμ Q a β u hu b).integral_prod_left using 1
  funext J
  rfl

theorem quadraticBankPartition_physicalPurePalm_mean
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) :
    (∫ J, quadraticBankPartition μ a β u J ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) =
      Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2) := by
  haveI : IsProbabilityMeasure (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
    unfold valueConditionedLaw
    infer_instance
  change (∫ J, (∫ y : Vector (d+1), quadraticBankPoint μ a β u J y
    ∂sphereLaw (d+1)) ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b)=_
  rw [integral_integral_swap (quadraticBankPoint_prod_integrable_pure μ hμ Q a β u hu b)]
  have hh : (fun y : Vector (d+1) =>
      ∫ J, quadraticBankPoint μ a β u J y ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) =ᵐ[sphereLaw (d+1)]
      fun _ => Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2) := by
    filter_upwards [sphereLaw_support (by omega : 1≤d+1)] with y hy
    exact quadraticBankPoint_physicalPurePalm_mean μ hμ Q a β u hu b y hy
  rw [integral_congr_ae hh]
  simp

theorem quadraticBankPartition_physicalPurePalm_sq_integrable
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) :
    Integrable (fun J => (quadraticBankPartition μ a β u J)^2)
      (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
  convert (quadraticBankPoint_pair_prod_integrable_pure μ hμ Q a β u hu b).integral_prod_left using 1
  funext J
  exact quadraticBankPartition_sq_eq_pairIntegral μ a β u J

/-- Exact source replica identity for the actual Palm quadratic bank; the
Gaussian factor is the physical ambient dimension and the angular overlap
is normalized in the transverse dimension. -/
theorem quadraticBankPartition_physicalPurePalm_sq_mean
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) :
    (∫ J, (quadraticBankPartition μ a β u J)^2
      ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) =
      ∫ yz : Vector (d+1) × Vector (d+1),
        Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a *
          (1+(overlap yz.1 yz.2)^2))
        ∂(sphereLaw (d+1)).prod (sphereLaw (d+1)) := by
  haveI : IsProbabilityMeasure (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
    unfold valueConditionedLaw
    infer_instance
  simp_rw [quadraticBankPartition_sq_eq_pairIntegral]
  rw [integral_integral_swap
    (quadraticBankPoint_pair_prod_integrable_pure μ hμ Q a β u hu b)]
  apply integral_congr_ae
  filter_upwards [sphereLaw_pair_support (by omega : 1≤d+1)] with yz hyz
  have hpoint (J : Disorder (d+2) μ.maxDegree) :
      quadraticBankPoint μ a β u J yz.1 *
        quadraticBankPoint μ a β u J yz.2 =
        Real.exp (β*quadraticLatitudeJetPair μ a u
          (quadraticBankDirection (d+1) u yz.1)
          (quadraticBankDirection (d+1) u yz.2) J) := by
    unfold quadraticBankPoint quadraticLatitudeJetPair
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  exact quadraticLatitudeJetPair_physicalPurePalm_exp_integral_transverse
    μ hμ Q a β u hu yz.1 yz.2 hyz.1 hyz.2 b

/-- Source `mb-quadratic` second moment for the *literal* original-tensor
quadratic bank under the exact canonical mixed Palm posterior. The sole
analytic input is the spherical overlap factor bound; the Gaussian posterior
law, integrability, and replica Fubini steps have been proved above. -/
theorem quadraticBankPartition_physicalPurePalm_secondMoment_le_of_overlap
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β C : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ)
    (hoverlap : ∀ y : Vector (d+1), ‖y‖^2=((d+1:ℕ):ℝ) →
      (∫ z : Vector (d+1), Real.exp
        (β^2*sourceQuadraticLatitudeVariance μ a*((d+2:ℕ):ℝ)*
          (overlap y z)^2) ∂sphereLaw (d+1)) ≤ C) :
    (∫ J, (quadraticBankPartition μ a β u J)^2
      ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) ≤
      C*(∫ J, quadraticBankPartition μ a β u J
        ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b)^2 := by
  haveI : IsProbabilityMeasure (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
    unfold valueConditionedLaw
    infer_instance
  let t : ℝ := β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a
  let ν := (sphereLaw (d+1)).prod (sphereLaw (d+1))
  have hinner : Integrable (fun yz : Vector (d+1) × Vector (d+1) =>
      ∫ J, quadraticBankPoint μ a β u J yz.1 *
        quadraticBankPoint μ a β u J yz.2
        ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) ν :=
    (quadraticBankPoint_pair_prod_integrable_pure μ hμ Q a β u hu b).integral_prod_right
  have hfull : Integrable (fun yz : Vector (d+1) × Vector (d+1) =>
      Real.exp (t*(1+(overlap yz.1 yz.2)^2))) ν := by
    apply hinner.congr
    filter_upwards [sphereLaw_pair_support (by omega : 1≤d+1)] with yz hyz
    have hpoint (J : Disorder (d+2) μ.maxDegree) :
        quadraticBankPoint μ a β u J yz.1 *
          quadraticBankPoint μ a β u J yz.2 =
          Real.exp (β*quadraticLatitudeJetPair μ a u
            (quadraticBankDirection (d+1) u yz.1)
            (quadraticBankDirection (d+1) u yz.2) J) := by
      unfold quadraticBankPoint quadraticLatitudeJetPair
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [hpoint]
    simpa only [t,mul_assoc] using
      (quadraticLatitudeJetPair_physicalPurePalm_exp_integral_transverse
        μ hμ Q a β u hu yz.1 yz.2 hyz.1 hyz.2 b)
  have hfactor (yz : Vector (d+1) × Vector (d+1)) :
      Real.exp (t*(1+(overlap yz.1 yz.2)^2)) =
        Real.exp t * Real.exp (t*(overlap yz.1 yz.2)^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hoverlapInt : Integrable (fun yz : Vector (d+1) × Vector (d+1) =>
      Real.exp (t*(overlap yz.1 yz.2)^2)) ν := by
    have h : (fun yz : Vector (d+1) × Vector (d+1) =>
        Real.exp (t*(overlap yz.1 yz.2)^2)) =
        (fun yz => Real.exp (-t)*Real.exp (t*(1+(overlap yz.1 yz.2)^2))) := by
      funext yz
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h]
    exact hfull.const_mul _
  have hreplica : (∫ yz : Vector (d+1) × Vector (d+1),
      Real.exp (t*(overlap yz.1 yz.2)^2) ∂ν) ≤ C := by
    rw [integral_prod _ hoverlapInt]
    calc
      _ ≤ ∫ _y : Vector (d+1), C ∂sphereLaw (d+1) := by
        apply integral_mono_ae hoverlapInt.integral_prod_left (integrable_const C)
        filter_upwards [sphereLaw_support (by omega : 1≤d+1)] with y hy
        have he : (fun z : Vector (d+1) =>
            Real.exp (t*(overlap y z)^2)) =
            (fun z => Real.exp
              (β^2*sourceQuadraticLatitudeVariance μ a*((d+2:ℕ):ℝ)*
                (overlap y z)^2)) := by
          funext z
          congr 1
          dsimp [t]
          ring
        rw [he]
        exact hoverlap y hy
      _ = C := by simp
  rw [quadraticBankPartition_physicalPurePalm_sq_mean μ hμ Q a β u hu b,
    quadraticBankPartition_physicalPurePalm_mean μ hμ Q a β u hu b]
  have hfactIntegral :
      (∫ yz : Vector (d+1) × Vector (d+1),
        Real.exp (t*(1+(overlap yz.1 yz.2)^2)) ∂ν) =
        Real.exp t * (∫ yz : Vector (d+1) × Vector (d+1),
          Real.exp (t*(overlap yz.1 yz.2)^2) ∂ν) := by
    simp_rw [hfactor]
    rw [integral_const_mul]
  change (∫ yz : Vector (d+1) × Vector (d+1),
    Real.exp (t*(1+(overlap yz.1 yz.2)^2)) ∂ν) ≤
      C*(Real.exp (t/2))^2
  rw [hfactIntegral]
  have hsq : (Real.exp (t/2))^2=Real.exp t := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [hsq]
  exact (mul_le_mul_of_nonneg_left hreplica (Real.exp_pos t).le).trans_eq
    (mul_comm _ _)

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
