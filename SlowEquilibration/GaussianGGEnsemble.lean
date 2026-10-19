-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianReplicaKernel
public import SlowEquilibration.GaussianGGStarRecursion
public import SlowEquilibration.GaussianGGWeights

/-! Actual disorder-averaged IID Gibbs replicas, overlap laws and hard
negative-star expectations. Prefix/pair consistency, unit-ball support,
the geometric star bound and the hard-star recursion are all derived
from the ordinary Markov law. Only tested Gaussian GG defects remain
for the model-specific Gaussian integration-by-parts proof. -/

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

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- The true overlap kernel under two independent conditional spins. -/
def overlapKernel (G : Kernel Ω H) : Kernel Ω ℝ :=
  (G ×ₖ G).map (fun z => inner ℝ z.1 z.2)

omit [CompleteSpace H] in
theorem overlap_map_measurable : Measurable (fun z : H × H => inner ℝ z.1 z.2) :=
  (continuous_fst.inner continuous_snd).measurable

instance overlapKernel_markov (G : Kernel Ω H) [IsMarkovKernel G] : IsMarkovKernel (overlapKernel G) :=
  Kernel.IsMarkovKernel.map _ overlap_map_measurable

def overlapLaw (d : Measure Ω) (G : Kernel Ω H) : Measure ℝ := overlapKernel G ∘ₘ d

instance overlapLaw_probability (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] : IsProbabilityMeasure (overlapLaw d G) := by
  unfold overlapLaw
  infer_instance

omit [CompleteSpace H] in
/-- Every true distinct-coordinate overlap has the same actual averaged
pair law, obtained from ordinary independent conditional sampling. -/
theorem overlap_hasLaw (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G]
    {n : ℕ} (i j : Fin n) (hij : i≠j) :
    HasLaw (fun σ : Fin n → H => inner ℝ (σ i) (σ j))
      (overlapLaw d G) (GaussianReplicaKernel.law d G n) := by
  have hpair := GaussianReplicaKernel.pair_hasLaw d G i j hij
  have hinner : HasLaw (fun z : H × H => inner ℝ z.1 z.2) (overlapLaw d G) ((G ×ₖ G) ∘ₘ d) := by
    refine ⟨overlap_map_measurable.aemeasurable,?_⟩
    rw [Measure.map_comp _ _ overlap_map_measurable]
    rfl
  exact hinner.fun_comp hpair

omit [CompleteSpace H] in
/-- Unit-ball conditional Gibbs support gives the literal overlap support. -/
theorem overlapLaw_ae_Icc (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G]
    (hG : ∀ᵐ ω ∂d, ∀ᵐ z ∂G ω, ‖z‖≤1) :
    ∀ᵐ r ∂overlapLaw d G, r∈Icc (-1:ℝ) 1 := by
  apply Measure.ae_comp_of_ae_ae (show MeasurableSet {r : ℝ | r∈Icc (-1:ℝ) 1} from measurableSet_Icc)
  filter_upwards [hG] with ω hω
  rw [overlapKernel,Kernel.map_apply _ overlap_map_measurable,Kernel.prod_apply]
  apply (ae_map_iff overlap_map_measurable.aemeasurable measurableSet_Icc).mpr
  apply (Measure.ae_prod_iff_ae_ae (overlap_map_measurable measurableSet_Icc)).mpr
  filter_upwards [hω] with x hx
  filter_upwards [hω] with y hy
  have hi : |inner ℝ x y|≤1 := (abs_real_inner_le_norm x y).trans (by
    simpa only [one_mul] using mul_le_mul hx hy (norm_nonneg y) (by norm_num : (0:ℝ)≤1))
  exact abs_le.mp hi

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [BorelSpace H] in
/-- Ordinary event-mass disintegration for the genuine replica kernel. -/
theorem replicaLaw_real_eq_integral (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G]
    (n : ℕ) (A : Set (Fin n → H)) (hA : MeasurableSet A) :
    (GaussianReplicaKernel.law d G n).real A=
      ∫ω,(Measure.pi (fun _ : Fin n => G ω)).real A ∂d := by
  rw [GaussianReplicaKernel.law,Measure.real,
    Measure.bind_apply hA (GaussianReplicaKernel.iid G n).aemeasurable,
    ← integral_toReal ((GaussianReplicaKernel.iid G n).measurable_coe hA).aemeasurable
      (.of_forall (fun ω => by finiteness))]
  simp only [GaussianReplicaKernel.iid_apply,Measure.real]

/-- The true averaged m-neighbor star probability. -/
def starMass (d : Measure Ω) (G : Kernel Ω H) (ε : ℝ) (m : ℕ) : ℝ :=
  (GaussianReplicaKernel.law d G (m+1)).real (negativeStar ε m)

omit [CompleteSpace H] in
theorem starMass_eq_integral (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G]
    (ε : ℝ) (m : ℕ) :
    starMass d G ε m=∫ω,(Measure.pi (fun _ : Fin (m+1) => G ω)).real (negativeStar ε m) ∂d :=
  replicaLaw_real_eq_integral d G (m+1) _ (negativeStar_measurable ε m)

/-- Panchenko's actual geometric bound survives disorder averaging. -/
theorem starMass_le_geometric (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G]
    (hG : ∀ᵐ ω ∂d, ∀ᵐ z ∂G ω, ‖z‖≤1)
    {ε γ : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hγ : 0<γ) (hγ1 : γ<1) (m : ℕ) :
    starMass d G ε m≤2*(1-γ)/ε+γ^m := by
  rw [starMass_eq_integral]
  have hi : Integrable (fun ω => (Measure.pi (fun _ : Fin (m+1) => G ω)).real (negativeStar ε m)) d := by
    have hm : Measurable (fun ω => (Measure.pi (fun _ : Fin (m+1) => G ω)).real (negativeStar ε m)) := by
      simpa only [GaussianReplicaKernel.iid_apply,Measure.real] using
        ((GaussianReplicaKernel.iid G (m+1)).measurable_coe (negativeStar_measurable ε m)).ennreal_toReal
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall fun ω => by
      change ‖(Measure.pi (fun _ : Fin (m+1) => G ω)).real (negativeStar ε m)‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have ht := integral_mono_ae hi (integrable_const (2*(1-γ)/ε+γ^m))
    (hG.mono fun ω hω => negativeStar_mass_le (G ω) hω hε hε1 hγ hγ1 m)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ht

omit [CompleteSpace H] in
theorem starObservable_integral (d : Measure Ω) (G : Kernel Ω H)
    (ε : ℝ) (m : ℕ) :
    (∫σ,starObservable ε m σ ∂GaussianReplicaKernel.law d G (m+1))=starMass d G ε m := by
  change (∫σ,(negativeStar ε m).indicator (fun _ => (1:ℝ)) σ
    ∂GaussianReplicaKernel.law d G (m+1))=_
  rw [integral_indicator_const 1 (negativeStar_measurable ε m),smul_eq_mul,mul_one]
  rfl

omit [CompleteSpace H] in
/-- The original star observable under m+2 replicas has exactly the
m-neighbor star mean, by true prefix consistency. -/
theorem prefixStar_integral (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G]
    (ε : ℝ) (m : ℕ) :
    (∫σ,prefixStar ε m σ ∂GaussianReplicaKernel.law d G (m+2))=starMass d G ε m := by
  have h := (GaussianReplicaKernel.initial_hasLaw d G (m+1)).integral_comp
    (starObservable_measurable ε m).aestronglyMeasurable
  calc
    _ = ∫σ,starObservable ε m σ ∂GaussianReplicaKernel.law d G (m+1) := h
    _ = _ := starObservable_integral d G ε m

omit [CompleteSpace H] in
/-- The one-neighbor probability equals the ordinary overlap-law mass. -/
theorem starMass_one (d : Measure Ω) (G : Kernel Ω H) [IsMarkovKernel G] (ε : ℝ) :
    starMass d G ε 1=(overlapLaw d G).real (Iic (-ε)) := by
  have h := (overlap_hasLaw d G (0 : Fin 2) 1 (by decide)).measureReal_eq
    (p := fun r => r≤-ε) measurableSet_Iic
  have hset : {σ : Fin 2 → H | inner ℝ (σ 0) (σ 1)≤-ε}=negativeStar ε 1 := by
    ext σ
    simp only [negativeStar,mem_ofPred_eq,Fin.forall_fin_one,Fin.succ_zero_eq_one]
  rw [hset] at h
  exact h

/-- The actual tested-power GG defect used by Gaussian IBP. -/
def powerDefect (d : Measure Ω) (G : Kernel Ω H) (ε : ℝ) (m p : ℕ) : ℝ :=
  |discrepancy m (GaussianReplicaKernel.law d G (m+2)) (overlapLaw d G)
    (prefixStar ε m) (freshOverlap m) (oldOverlap m) (fun r => r^p)|

omit [CompleteSpace H] in
/-- Exact recursion for the genuine disorder-averaged IID stars. -/
theorem star_recursion_discrepancy (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    (ε : ℝ) (m : ℕ) :
    discrepancy m (GaussianReplicaKernel.law d G (m+2)) (overlapLaw d G)
      (prefixStar ε m) (freshOverlap m) (oldOverlap m) (negativeStep ε)=
      starMass d G ε (m+1)-(((m:ℝ)+starMass d G ε 1)/((m:ℝ)+1))*starMass d G ε m := by
  have ht := discrepancy_star_recursion (GaussianReplicaKernel.law d G (m+2))
    (overlapLaw d G) m ε id
  simpa only [Function.id_def,starObservable_integral,prefixStar_integral,starMass_one] using ht

omit [CompleteSpace H] in
/-- The actual finite power defects control the true IID star recursion. -/
theorem star_recursion_le_powerDefects (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G]
    (hG : ∀ᵐ ω ∂d, ∀ᵐ z ∂G ω, ‖z‖≤1)
    (m : ℕ) {ε : ℝ} {M : ℕ} (hε : 0<ε) (hM : 0<M) (j : Fin M)
    (P : Polynomial ℝ) {K : ℕ} (hK : P.natDegree≤K) {δ : ℝ} (hδ : 0≤δ)
    (happrox : ∀r∈Icc (-1:ℝ) 1, |P.eval r-cutoff ε M j r|≤δ) :
    |starMass d G (-leftEndpoint ε M j) (m+1)-
      (((m:ℝ)+starMass d G (-leftEndpoint ε M j) 1)/((m:ℝ)+1))*
        starMass d G (-leftEndpoint ε M j) m|≤
      (∑p∈Finset.range (K+1), |P.coeff p| * powerDefect d G (-leftEndpoint ε M j) m p)+
        2*δ+2*(overlapLaw d G).real (shell ε M j) := by
  have hR : HasLaw (freshOverlap (H := H) m) (overlapLaw d G)
      (GaussianReplicaKernel.law d G (m+2)) :=
    overlap_hasLaw d G 0 (Fin.last (m+1)) (by intro h;have hv := congrArg Fin.val h; simp at hv)
  have hQ (j : Fin m) : HasLaw (oldOverlap (H := H) m j) (overlapLaw d G)
      (GaussianReplicaKernel.law d G (m+2)) :=
    overlap_hasLaw d G 0 j.succ.castSucc (by intro h;have hv := congrArg Fin.val h; simp at hv)
  have ht := star_recursion_error_le (GaussianReplicaKernel.law d G (m+2)) (overlapLaw d G)
    m id measurable_id hR hQ (overlapLaw_ae_Icc d G hG) hε hM j P hK hδ happrox
    (powerDefect d G (-leftEndpoint ε M j) m) (fun p hp => le_rfl)
  have hOne : starMass d G (-leftEndpoint ε M j) 1=
      (overlapLaw d G).real (Iic (leftEndpoint ε M j)) := by
    simpa only [neg_neg] using starMass_one d G (-leftEndpoint ε M j)
  rw [← hOne] at ht
  simpa only [Function.id_def,starObservable_integral,prefixStar_integral] using ht

end SlowEquilibration.GaussianGGEnsemble
