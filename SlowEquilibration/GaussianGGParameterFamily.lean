-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGEnsemble

/-! Genuine parameter-indexed replica and overlap kernels. Gaussian
averaging is performed conditionally at each perturbation parameter;
its outer parameter average is kept separate from the GG product term. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGEnsemble

open MeasureTheory ProbabilityTheory Set
open GaussianNegativeStarGeometry GaussianGGIndicatorTransfer
open GaussianGGCutoffs GaussianGGPolynomialTests GaussianGGStarRecursion
open scoped ProbabilityTheory Topology BigOperators

set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Average
variable {X Ω V : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace V]

/-- Average an actual joint kernel over disorder, retaining its external
perturbation parameter as the kernel input. -/
def disorderAverage (d : Measure Ω) (F : Kernel (X × Ω) V) : Kernel X V :=
  (Kernel.const X d ⊗ₖ F).snd

instance disorderAverage_markov (d : Measure Ω) [IsProbabilityMeasure d]
    (F : Kernel (X × Ω) V) [IsMarkovKernel F] : IsMarkovKernel (disorderAverage d F) := by
  unfold disorderAverage
  infer_instance

theorem disorderAverage_apply (d : Measure Ω) [IsProbabilityMeasure d]
    (F : Kernel (X × Ω) V) [IsMarkovKernel F] (x : X) :
    disorderAverage d F x=(Kernel.sectR F x) ∘ₘ d := by
  change ((Kernel.const X d ⊗ₖ F) x).snd=_
  rw [Kernel.compProd_apply_eq_compProd_sectR,Kernel.const_apply,Measure.snd_compProd]

 theorem iid_sectR (G : Kernel (X × Ω) V) [IsMarkovKernel G] (n : ℕ) (x : X) :
    (GaussianReplicaKernel.iid G n).sectR x=GaussianReplicaKernel.iid (G.sectR x) n := by
  apply Kernel.ext
  intro ω
  rw [Kernel.sectR_apply,GaussianReplicaKernel.iid_apply,GaussianReplicaKernel.iid_apply]
  rfl

/-- Actual parameter kernel of disorder-averaged IID replicas. -/
def replicaFamily (d : Measure Ω) (G : Kernel (X × Ω) V) (n : ℕ) : Kernel X (Fin n → V) :=
  disorderAverage d (GaussianReplicaKernel.iid G n)

instance replicaFamily_markov (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel (X × Ω) V) [IsMarkovKernel G] (n : ℕ) : IsMarkovKernel (replicaFamily d G n) := by
  unfold replicaFamily
  infer_instance

 theorem replicaFamily_apply (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel (X × Ω) V) [IsMarkovKernel G] (n : ℕ) (x : X) :
    replicaFamily d G n x=GaussianReplicaKernel.law d (G.sectR x) n := by
  rw [replicaFamily,disorderAverage_apply,iid_sectR]
  rfl
end Average

variable {X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

 theorem overlapKernel_sectR (G : Kernel (X × Ω) H) [IsMarkovKernel G] (x : X) :
    (overlapKernel G).sectR x=overlapKernel (G.sectR x) := by
  apply Kernel.ext
  intro ω
  simp only [Kernel.sectR_apply,overlapKernel,Kernel.map_apply _ overlap_map_measurable,Kernel.prod_apply]

/-- The actual pair-law family, with Gaussian mean at fixed parameter. -/
def overlapFamily (d : Measure Ω) (G : Kernel (X × Ω) H) : Kernel X ℝ :=
  disorderAverage d (overlapKernel G)

instance overlapFamily_markov (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel (X × Ω) H) [IsMarkovKernel G] : IsMarkovKernel (overlapFamily d G) := by
  unfold overlapFamily
  infer_instance

 theorem overlapFamily_apply (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel (X × Ω) H) [IsMarkovKernel G] (x : X) :
    overlapFamily d G x=overlapLaw d (G.sectR x) := by
  rw [overlapFamily,disorderAverage_apply,overlapKernel_sectR]
  rfl

 theorem starMass_measurable (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel (X × Ω) H) [IsMarkovKernel G] (ε : ℝ) (m : ℕ) :
    Measurable (fun x => starMass d (G.sectR x) ε m) := by
  simpa only [replicaFamily_apply,Measure.real,starMass] using
    ((replicaFamily d G (m+1)).measurable_coe (negativeStar_measurable ε m)).ennreal_toReal

/-- Every tested power discrepancy is a Borel function of the true
external parameter, through the actual probability kernels. -/
theorem powerDefect_measurable (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel (X × Ω) H) [IsMarkovKernel G] (ε : ℝ) (m p : ℕ) :
    Measurable (fun x => powerDefect d (G.sectR x) ε m p) := by
  have hF : Measurable (fun x => ∫σ,prefixStar ε m σ ∂GaussianReplicaKernel.law d (G.sectR x) (m+2)) := by
    simpa only [replicaFamily_apply] using
      ((prefixStar_measurable ε m).stronglyMeasurable.integral_kernel (κ := replicaFamily d G (m+2))).measurable
  have hP : Measurable (fun x => ∫r,r^p ∂overlapLaw d (G.sectR x)) := by
    simpa only [overlapFamily_apply,Function.id_def] using
      ((measurable_id.pow_const p).stronglyMeasurable.integral_kernel (κ := overlapFamily d G)).measurable
  have hFresh : Measurable (fun x => ∫σ,prefixStar ε m σ*(freshOverlap m σ)^p
      ∂GaussianReplicaKernel.law d (G.sectR x) (m+2)) := by
    simpa only [replicaFamily_apply,Pi.mul_apply] using
      (((prefixStar_measurable ε m).mul ((freshOverlap_measurable m).pow_const p)).stronglyMeasurable.integral_kernel
        (κ := replicaFamily d G (m+2))).measurable
  have hOld (j : Fin m) : Measurable (fun x => ∫σ,prefixStar ε m σ*(oldOverlap m j σ)^p
      ∂GaussianReplicaKernel.law d (G.sectR x) (m+2)) := by
    simpa only [replicaFamily_apply,Pi.mul_apply] using
      (((prefixStar_measurable ε m).mul ((oldOverlap_measurable m j).pow_const p)).stronglyMeasurable.integral_kernel
        (κ := replicaFamily d G (m+2))).measurable
  have hD := ((hFresh.sub ((hF.mul hP).div_const ((m:ℝ)+1))).sub
    ((Finset.measurable_sum Finset.univ (fun j _ => hOld j)).div_const ((m:ℝ)+1))).norm
  simpa only [powerDefect,discrepancy,Real.norm_eq_abs,Pi.mul_apply,Pi.sub_apply] using hD

omit [SecondCountableTopology H] [BorelSpace H] in
theorem powerDefect_nonneg (d : Measure Ω) (G : Kernel Ω H) (ε : ℝ) (m p : ℕ) :
    0≤powerDefect d G ε m p := abs_nonneg _

/-- The actual Gaussian GG power defect is uniformly bounded by two
under true unit-ball Gibbs support. -/
theorem powerDefect_le_two (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G]
    (hG : ∀ᵐ ω ∂d, ∀ᵐ z ∂G ω, ‖z‖≤1) (ε : ℝ) (m p : ℕ) :
    powerDefect d G ε m p≤2 := by
  let μ := GaussianReplicaKernel.law d G (m+2)
  let ρ := overlapLaw d G
  have hρ := overlapLaw_ae_Icc d G hG
  have hb : ∀ᵐ r ∂ρ, |r^p|≤1 := hρ.mono fun r hr => by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr hr)
  have hi : Integrable (fun r : ℝ => r^p) ρ :=
    Integrable.of_bound (measurable_id.pow_const p).aestronglyMeasurable 1
      (hb.mono fun r h => by simpa only [Real.norm_eq_abs] using h)
  have hL : (∫r,|r^p| ∂ρ)≤1 := by
    have ht := integral_mono_ae hi.abs (integrable_const (1:ℝ)) hb
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ht
  have hf : AEStronglyMeasurable (prefixStar (H := H) ε m) μ :=
    (prefixStar_measurable ε m).aestronglyMeasurable
  have hfb : ∀ᵐ σ ∂μ, |prefixStar ε m σ|≤1 := .of_forall fun σ => by
    have hm := starObservable_mem ε m (replicaPrefix σ)
    change |starObservable ε m (replicaPrefix σ)|≤1
    rw [abs_of_nonneg hm.1]
    exact hm.2
  have hR : HasLaw (freshOverlap (H := H) m) ρ μ :=
    overlap_hasLaw d G 0 (Fin.last (m+1)) (by intro h;have hv := congrArg Fin.val h; simp at hv)
  have hQ (j : Fin m) : HasLaw (oldOverlap (H := H) m j) ρ μ :=
    overlap_hasLaw d G 0 j.succ.castSucc (by intro h;have hv := congrArg Fin.val h; simp at hv)
  exact (discrepancy_abs_le_l1 m μ ρ (prefixStar ε m) (freshOverlap m) (oldOverlap m)
    hf hfb hR hQ hi).trans (by nlinarith)

 theorem starMass_integrable (π : Measure X) [IsProbabilityMeasure π]
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel (X × Ω) H) [IsMarkovKernel G]
    (ε : ℝ) (m : ℕ) : Integrable (fun x => starMass d (G.sectR x) ε m) π := by
  apply Integrable.of_bound (starMass_measurable d G ε m).aestronglyMeasurable 1
  exact .of_forall fun x => by
    change ‖(GaussianReplicaKernel.law d (G.sectR x) (m+1)).real (negativeStar ε m)‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

 theorem powerDefect_integrable (π : Measure X) [IsProbabilityMeasure π]
    (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel (X × Ω) H) [IsMarkovKernel G]
    (hG : ∀ᵐ x ∂π, ∀ᵐ ω ∂d, ∀ᵐ z ∂G (x,ω), ‖z‖≤1)
    (ε : ℝ) (m p : ℕ) : Integrable (fun x => powerDefect d (G.sectR x) ε m p) π := by
  apply Integrable.of_bound (powerDefect_measurable d G ε m p).aestronglyMeasurable 2
  filter_upwards [hG] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (powerDefect_nonneg _ _ _ _ _)]
  exact powerDefect_le_two d (G.sectR x) hx ε m p

end SlowEquilibration.GaussianGGEnsemble
