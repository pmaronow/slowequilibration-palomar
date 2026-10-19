-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGPowerResponse
public import SlowEquilibration.GaussianReplicaTransport
public import SlowEquilibration.GaussianSpinKernels

/-! Exact identification of the Gaussian tested-power GG discrepancy
with the original ordinary ambient IID replica discrepancy. The Gibbs
kernel and all spin transports are the actual measurable constructions;
no kernel-identification hypothesis is supplied. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianReplicaCalculus

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianGGIndicatorTransfer GaussianGGEnsemble
open GaussianGGStarRecursion
open scoped ProbabilityTheory Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Actual finite Gaussian Gibbs expectations equal the ordinary
integral under the constructed Gaussian-averaged IID kernel law. -/
theorem meanReplica_eq_integral_law (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (n : ℕ) (f : (Fin n → V) → ℝ) (hf : Measurable f) {C : ℝ} (hfb : ∀σ,‖f σ‖≤C) :
    meanReplica ν L n f=∫σ,f σ ∂GaussianReplicaKernel.law
      (SYK.standardGaussianMeasureOnEuclidean ι) (gibbsKernel ν L) n := by
  let _ := gibbsKernel_markov ν L hL hK hb
  rw [GaussianReplicaKernel.integral_law _ _ n f hf hfb]
  simp_rw [gibbsKernel_apply ν L hL hK hb]
  rfl

omit [DecidableEq ι] in
/-- Intrinsic-to-ambient replica transport retains the true probability
law and its original Gaussian mean. Only the transported test is used. -/
theorem meanReplica_transport {W : Type*} [MeasurableSpace W]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (s : V → W) (hs : Measurable s) (n : ℕ) (f : (Fin n → W) → ℝ) (hf : Measurable f)
    {C : ℝ} (hfb : ∀σ : Fin n → V, ‖f (GaussianReplicaKernel.mapReplicas s n σ)‖≤C) :
    meanReplica ν L n (fun σ => f (GaussianReplicaKernel.mapReplicas s n σ))=
      ∫σ,f σ ∂GaussianReplicaKernel.law (SYK.standardGaussianMeasureOnEuclidean ι)
        ((gibbsKernel ν L).map s) n := by
  let _ := gibbsKernel_markov ν L hL hK hb
  have hmf : Measurable (fun σ => f (GaussianReplicaKernel.mapReplicas s n σ)) := by
    simpa only [Function.comp_def] using hf.comp (GaussianReplicaKernel.mapReplicas_measurable hs n)
  rw [meanReplica_eq_integral_law ν L hL hK hb n _ hmf hfb]
  exact (GaussianReplicaKernel.mapReplicas_hasLaw _ (gibbsKernel ν L) s hs n).integral_comp hf.aestronglyMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

omit [DecidableEq ι] in
/-- The actual normalized raw Gaussian power-GG expression equals the
literal ordinary ambient replica discrepancy used by finite positivity. -/
theorem powerGG_eq_ambient_discrepancy (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (s : V → H) (hs : Measurable s) (hS : ∀z,‖s z‖≤1)
    (m p : ℕ) (f : (Fin (m+1) → H) → ℝ) (hf : Measurable f) (hfb : ∀σ,|f σ|≤1) :
    powerGG ν L (fun z y => inner ℝ (s z) (s y)) m p
      (fun σ => f (GaussianReplicaKernel.mapReplicas s (m+1) σ))=
    discrepancy m
      (GaussianReplicaKernel.law (SYK.standardGaussianMeasureOnEuclidean ι) ((gibbsKernel ν L).map s) (m+2))
      (overlapLaw (SYK.standardGaussianMeasureOnEuclidean ι) ((gibbsKernel ν L).map s))
      (fun σ => f (initialReplicas σ)) (freshOverlap m) (oldOverlap m) (fun r => r^p) := by
  classical
  let d := SYK.standardGaussianMeasureOnEuclidean ι
  let G := (gibbsKernel ν L).map s
  let _ := gibbsKernel_markov ν L hL hK hb
  let _ : IsMarkovKernel G := Kernel.IsMarkovKernel.map _ hs
  let μ := GaussianReplicaKernel.law d G (m+2)
  let ρ := overlapLaw d G
  have hinner (z y : V) : |inner ℝ (s z) (s y)|≤1 := (abs_real_inner_le_norm _ _).trans (by
    simpa only [one_mul] using mul_le_mul (hS z) (hS y) (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
  have hp (z y : V) : |(inner ℝ (s z) (s y))^p|≤1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hinner z y)
  let newTest : (Fin (m+2) → H) → ℝ := fun σ => f (initialReplicas σ)*(freshOverlap m σ)^p
  have hnew : Measurable newTest := by
    simpa only [newTest,Function.comp_def] using measurable_mul.comp
      ((hf.comp (initialReplicas_measurable (m+1))).prodMk ((freshOverlap_measurable m).pow_const p))
  have hnBound (σ : Fin (m+2) → V) : ‖newTest (GaussianReplicaKernel.mapReplicas s (m+2) σ)‖≤1 := by
    change |f (initialReplicas (GaussianReplicaKernel.mapReplicas s (m+2) σ))*
      (inner ℝ (s (σ 0)) (s (σ (Fin.last (m+1)))))^p|≤1
    rw [abs_mul]
    exact (mul_le_mul (hfb _) (hp _ _) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (by ring)
  have hnewMean := meanReplica_transport ν L hL hK hb s hs (m+2) newTest hnew hnBound
  let pairTest : (Fin 2 → H) → ℝ := fun σ => (inner ℝ (σ 0) (σ 1))^p
  have hpair : Measurable pairTest :=
    (((continuous_apply 0).inner (continuous_apply 1)).measurable).pow_const p
  have hpBound (σ : Fin 2 → V) : ‖pairTest (GaussianReplicaKernel.mapReplicas s 2 σ)‖≤1 := by
    change |(inner ℝ (s (σ 0)) (s (σ 1)))^p|≤1
    exact hp _ _
  have hpairMean := meanReplica_transport ν L hL hK hb s hs 2 pairTest hpair hpBound
  have hpairLaw := (overlap_hasLaw d G (0 : Fin 2) 1 (by decide)).integral_comp
    (measurable_id.pow_const p).aestronglyMeasurable
  change (∫σ,pairTest σ ∂GaussianReplicaKernel.law (SYK.standardGaussianMeasureOnEuclidean ι)
    ((gibbsKernel ν L).map s) 2)=(∫r,r^p ∂overlapLaw (SYK.standardGaussianMeasureOnEuclidean ι)
    ((gibbsKernel ν L).map s)) at hpairLaw
  have hFMean := meanReplica_transport ν L hL hK hb s hs (m+1) f hf
    (fun σ => by simpa only [Real.norm_eq_abs] using hfb _)
  have hprefixMean := (GaussianReplicaKernel.initial_hasLaw d G (m+1)).integral_comp hf.aestronglyMeasurable
  change (∫σ,f (initialReplicas σ) ∂GaussianReplicaKernel.law
    (SYK.standardGaussianMeasureOnEuclidean ι) ((gibbsKernel ν L).map s) (m+2))=
    (∫σ,f σ ∂GaussianReplicaKernel.law (SYK.standardGaussianMeasureOnEuclidean ι)
      ((gibbsKernel ν L).map s) (m+1)) at hprefixMean
  let oldTest (j : Fin m) : (Fin (m+1) → H) → ℝ := fun σ => f σ*(inner ℝ (σ 0) (σ j.succ))^p
  have holdMeas (j : Fin m) : Measurable (oldTest j) := by
    have hi : Measurable (fun σ : Fin (m+1) → H => (inner ℝ (σ 0) (σ j.succ))^p) :=
      (((continuous_apply 0).inner (continuous_apply j.succ)).measurable).pow_const p
    simpa only [oldTest,Function.comp_def] using measurable_mul.comp (hf.prodMk hi)
  have hoBound (j : Fin m) (σ : Fin (m+1) → V) : ‖oldTest j (GaussianReplicaKernel.mapReplicas s (m+1) σ)‖≤1 := by
    change |f (GaussianReplicaKernel.mapReplicas s (m+1) σ)*(inner ℝ (s (σ 0)) (s (σ j.succ)))^p|≤1
    rw [abs_mul]
    exact (mul_le_mul (hfb _) (hp _ _) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (by ring)
  have holdMean (j : Fin m) := meanReplica_transport ν L hL hK hb s hs (m+1) (oldTest j) (holdMeas j) (hoBound j)
  have holdPrefix (j : Fin m) := (GaussianReplicaKernel.initial_hasLaw d G (m+1)).integral_comp (holdMeas j).aestronglyMeasurable
  have holdPrefix' (j : Fin m) :
      (∫σ,f (initialReplicas σ)*(oldOverlap m j σ)^p ∂GaussianReplicaKernel.law
        (SYK.standardGaussianMeasureOnEuclidean ι) ((gibbsKernel ν L).map s) (m+2))=
      (∫σ,oldTest j σ ∂GaussianReplicaKernel.law (SYK.standardGaussianMeasureOnEuclidean ι)
        ((gibbsKernel ν L).map s) (m+1)) := holdPrefix j
  unfold powerGG covarianceGG
  change meanReplica ν L (m+2) (fun σ => newTest (GaussianReplicaKernel.mapReplicas s (m+2) σ))-
    meanReplica ν L (m+1) (fun σ => f (GaussianReplicaKernel.mapReplicas s (m+1) σ))*
      meanReplica ν L 2 (fun σ => pairTest (GaussianReplicaKernel.mapReplicas s 2 σ))/((m:ℝ)+1)-
    (∑j : Fin m,meanReplica ν L (m+1) (fun σ => oldTest j (GaussianReplicaKernel.mapReplicas s (m+1) σ)))/((m:ℝ)+1)=_
  rw [hnewMean,hFMean,hpairMean]
  simp_rw [holdMean]
  rw [hpairLaw,← hprefixMean]
  simp_rw [← holdPrefix']
  rfl

omit [DecidableEq ι] in
/-- Direct identity for the actual hard-star tests of the finite
positivity consumer, including intrinsic-to-ambient unit-spin transport. -/
theorem powerGG_abs_eq_powerDefect (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K)
    (s : V → H) (hs : Measurable s) (hS : ∀z,‖s z‖≤1) (ε : ℝ) (m p : ℕ) :
    |powerGG ν L (fun z y => inner ℝ (s z) (s y)) m p
      (fun σ => starObservable ε m (GaussianReplicaKernel.mapReplicas s (m+1) σ))|=
      powerDefect (SYK.standardGaussianMeasureOnEuclidean ι) ((gibbsKernel ν L).map s) ε m p := by
  rw [powerGG_eq_ambient_discrepancy ν L hL hK hb s hs hS m p (starObservable ε m)
    (starObservable_measurable ε m) (fun σ => by
      have hmem := starObservable_mem ε m σ
      rw [abs_of_nonneg hmem.1]
      exact hmem.2)]
  rfl

end SlowEquilibration.GaussianReplicaCalculus
