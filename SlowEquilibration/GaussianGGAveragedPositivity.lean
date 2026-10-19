-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGFinitePositivity

/-! A single predetermined negative cutoff is selected using the actual
pair law averaged over perturbation parameters. Gaussian GG products
remain at fixed parameter. The final finite estimate depends only on
averaged literal power discrepancies, with no pointwise-in-parameter GG
smallness premise. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGEnsemble

open MeasureTheory ProbabilityTheory Set
open GaussianNegativeStarGeometry GaussianGGIndicatorTransfer
open GaussianGGCutoffs GaussianGGPolynomialTests GaussianGGStarRecursion
open scoped ProbabilityTheory Topology BigOperators

set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Mean
variable {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]

theorem kernel_real_mean (π : Measure X) (F : Kernel X V) [IsMarkovKernel F]
    (A : Set V) (hA : MeasurableSet A) :
    (F ∘ₘ π).real A=∫x,(F x).real A ∂π := by
  rw [Measure.real,Measure.bind_apply hA F.aemeasurable,
    ← integral_toReal (F.measurable_coe hA).aemeasurable (.of_forall (fun x => by finiteness))]
  rfl
end Mean

variable {X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- A literal finite sum of averaged Gaussian power-GG defects. All
star thresholds, replica counts and tested powers are fixed beforehand. -/
def finitePowerError (π : Measure X) (d : Measure Ω) (G : Kernel (X × Ω) H)
    (ε : ℝ) (n M K : ℕ) : ℝ :=
  ∑m∈Finset.Ico 1 n, ∑j : Fin M, ∑p∈Finset.range (K+1),
    ∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M j) m p ∂π

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
 theorem finitePowerError_nonneg (π : Measure X) (d : Measure Ω) (G : Kernel (X × Ω) H)
    (ε : ℝ) (n M K : ℕ) : 0≤finitePowerError π d G ε n M K := by
  unfold finitePowerError
  apply Finset.sum_nonneg
  intro m hm
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro p hp
  exact integral_nonneg fun x => powerDefect_nonneg _ _ _ _ _

/-- Model-independent finite averaged positivity estimate. The only
errors are actual tested-power discrepancies, uniform approximation,
and the predetermined disjoint-shell family. -/
theorem averaged_pair_mass_le_polynomial_errors
    (π : Measure X) [IsProbabilityMeasure π] (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel (X × Ω) H) [IsMarkovKernel G]
    (hG : ∀ᵐ x ∂π, ∀ᵐ ω ∂d, ∀ᵐ z ∂G (x,ω), ‖z‖≤1)
    {ε η : ℝ} (hε : 0<ε) (hε1 : ε≤1)
    (n : ℕ) (γ C : ℝ) (hγ : γ∈Ioo (0:ℝ) 1) (hC : 0≤C)
    (hNumeric : NumericExclusion (ε/2) η n γ C)
    (M : ℕ) (hM : 0<M) (P : Fin M → Polynomial ℝ) (K : ℕ)
    (hK : ∀j, (P j).natDegree≤K) (Ccoef : ℝ) (hCcoef : 0≤Ccoef)
    (hcoef : ∀j, (∑p∈Finset.range (K+1), |(P j).coeff p|)≤Ccoef)
    {δ : ℝ} (hδ : 0≤δ)
    (happrox : ∀j r, r∈Icc (-1:ℝ) 1 → |(P j).eval r-cutoff ε M j r|≤δ) :
    (∫x,starMass d (G.sectR x) ε 1 ∂π)≤
      η+C*(Ccoef*finitePowerError π d G ε n M K+(n:ℝ)*(2*δ+2/(M:ℝ))) := by
  classical
  let F := overlapFamily d G
  let ρ := F ∘ₘ π
  obtain ⟨j,hj⟩ := exists_shell_mass_le ρ hε hM
  have hShell : (∫x,(overlapLaw d (G.sectR x)).real (shell ε M j) ∂π)≤1/(M:ℝ) := by
    have hmean := kernel_real_mean π F (shell ε M j) measurableSet_Ioo
    simpa only [F,overlapFamily_apply] using hmean.symm.trans_le hj
  let r : X → ℝ := fun x => (overlapLaw d (G.sectR x)).real (shell ε M j)
  have hir : Integrable r π := by
    have hm : Measurable r := by
      simpa only [r,F,overlapFamily_apply,Measure.real] using
        (F.measurable_coe (show MeasurableSet (shell ε M j) from measurableSet_Ioo)).ennreal_toReal
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  let weighted (m : ℕ) : X → ℝ := fun x =>
    ∑p∈Finset.range (K+1), |(P j).coeff p| * powerDefect d (G.sectR x) (-leftEndpoint ε M j) m p
  have hiw (m : ℕ) : Integrable (weighted m) π := by
    apply integrable_finsetSum
    intro p hp
    exact (powerDefect_integrable π d G hG _ m p).const_mul _
  let errors (m : ℕ) : X → ℝ := fun x => weighted m x+2*δ+2*r x
  have hid (m : ℕ) : Integrable (errors m) π :=
    ((hiw m).add (integrable_const (2*δ))).add (hir.const_mul 2)
  let total : X → ℝ := fun x => ∑m∈Finset.Ico 1 n, errors m x
  have hitotal : Integrable total π := integrable_finsetSum _ (fun m hm => hid m)
  have hpoint : ∀ᵐ x ∂π, starMass d (G.sectR x) ε 1≤η+C*total x := by
    filter_upwards [hG] with x hx
    exact star_exclusion_of_numeric hε hε1 n γ C hγ hNumeric d (G.sectR x) hx M hM j (P j) K (hK j) δ hδ (happrox j)
  have hmean : (∫x,starMass d (G.sectR x) ε 1 ∂π)≤η+C*(∫x,total x ∂π) := by
    have ht := integral_mono_ae (starMass_integrable π d G ε 1)
      ((integrable_const η).add (hitotal.const_mul C)) hpoint
    have heq := integral_add (integrable_const (μ := π) η) (hitotal.const_mul C)
    rw [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul] at heq
    exact ht.trans_eq heq
  have hweighted_mean (m : ℕ) : (∫x,weighted m x ∂π)=
      ∑p∈Finset.range (K+1), |(P j).coeff p| *
        (∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M j) m p ∂π) := by
    rw [show weighted m=(fun x => ∑p∈Finset.range (K+1), |(P j).coeff p| *
      powerDefect d (G.sectR x) (-leftEndpoint ε M j) m p) from rfl]
    rw [integral_finsetSum _ (fun p hp => (powerDefect_integrable π d G hG _ m p).const_mul _)]
    simp_rw [integral_const_mul]
  have hwp (m : ℕ) : (∫x,weighted m x ∂π)≤Ccoef*(∑i : Fin M, ∑p∈Finset.range (K+1),
      ∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M i) m p ∂π) := by
    have hpnon (i : Fin M) (p : ℕ) : 0≤∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M i) m p ∂π :=
      integral_nonneg fun x => powerDefect_nonneg _ _ _ _ _
    have hsingle : (∑p∈Finset.range (K+1), ∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M j) m p ∂π)≤
        ∑i : Fin M, ∑p∈Finset.range (K+1), ∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M i) m p ∂π :=
      Finset.single_le_sum (fun i hi => Finset.sum_nonneg (fun p hp => hpnon i p)) (Finset.mem_univ j)
    rw [hweighted_mean]
    calc
      _ ≤ ∑p∈Finset.range (K+1), Ccoef*(∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M j) m p ∂π) := by
        apply Finset.sum_le_sum
        intro p hp
        have hcp : |(P j).coeff p|≤Ccoef :=
          (Finset.single_le_sum (fun p hp => abs_nonneg ((P j).coeff p)) hp).trans (hcoef j)
        exact mul_le_mul_of_nonneg_right hcp (hpnon j p)
      _ = Ccoef*(∑p∈Finset.range (K+1), ∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M j) m p ∂π) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsingle hCcoef
  have hDmean (m : ℕ) : (∫x,errors m x ∂π)≤
      Ccoef*(∑i : Fin M, ∑p∈Finset.range (K+1),
        ∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M i) m p ∂π)+2*δ+2/(M:ℝ) := by
    have heq : (∫x,errors m x ∂π)=(∫x,weighted m x ∂π)+2*δ+2*(∫x,r x ∂π) := by
      dsimp only [errors]
      have hB := integral_add ((hiw m).add (integrable_const (μ := π) (2*δ))) (hir.const_mul 2)
      have hA := integral_add (hiw m) (integrable_const (μ := π) (2*δ))
      simp only [Pi.add_apply] at hB hA
      rw [hB,hA,integral_const_mul 2 r]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [heq]
    have hscaled : 2*(∫x,r x ∂π)≤2/(M:ℝ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hShell (by norm_num : (0:ℝ)≤2)
    exact add_le_add (add_le_add (hwp m) (le_refl _)) hscaled
  have htotal : (∫x,total x ∂π)≤Ccoef*finitePowerError π d G ε n M K+(n:ℝ)*(2*δ+2/(M:ℝ)) := by
    rw [show total=(fun x => ∑m∈Finset.Ico 1 n,errors m x) from rfl,
      integral_finsetSum _ (fun m hm => hid m)]
    have hs := Finset.sum_le_sum (s := Finset.Ico 1 n) (fun m hm => hDmean m)
    have hcard : ((Finset.Ico 1 n).card:ℝ)≤(n:ℝ) := by
      norm_cast
      simp only [Nat.card_Ico]
      omega
    have hconst : 0≤2*δ+2/(M:ℝ) := by positivity
    calc
      _ ≤ ∑m∈Finset.Ico 1 n, (Ccoef*(∑i : Fin M, ∑p∈Finset.range (K+1),
        ∫x,powerDefect d (G.sectR x) (-leftEndpoint ε M i) m p ∂π)+2*δ+2/(M:ℝ)) := hs
      _ = Ccoef*finitePowerError π d G ε n M K+((Finset.Ico 1 n).card:ℝ)*(2*δ+2/(M:ℝ)) := by
        unfold finitePowerError
        simp_rw [show ∀a : ℝ, a+2*δ+2/(M:ℝ)=a+(2*δ+2/(M:ℝ)) from fun a => by ring]
        rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hconst)
  exact hmean.trans (add_le_add (le_refl η) (mul_le_mul_of_nonneg_left htotal hC))

end SlowEquilibration.GaussianGGEnsemble
