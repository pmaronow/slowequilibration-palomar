-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianGGParameterFamily

/-! Finite quantitative positivity from actual ordinary replica laws.
Numerical negative-star exclusion, real IID geometry and true
cutoff-to-polynomial transfer combine before any Gaussian model or
limiting dimension is chosen. The only errors are literal tested GG
power discrepancies and actual pair-law transition-shell masses. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGEnsemble

open MeasureTheory ProbabilityTheory Set
open GaussianNegativeStarGeometry GaussianGGIndicatorTransfer
open GaussianGGCutoffs GaussianGGPolynomialTests GaussianGGStarRecursion
open scoped ProbabilityTheory Topology BigOperators

set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Every selected negative step remains uniformly inside the prescribed
negative interval, with a positive threshold at least ε/2. -/
theorem selected_threshold_mem {ε : ℝ} {M : ℕ} (hε : 0<ε) (hM : 0<M) (j : Fin M) :
    -leftEndpoint ε M j∈Icc (ε/2) ε := by
  have he := endpoints_in_negative_band hε hM j
  have hw := width_pos hε hM
  have hr := right_eq_left_add_width ε M j
  constructor <;> linarith

omit [CompleteSpace H] in
/-- Literal pair-mass monotonicity relates the original negative event
to each predetermined selected step. -/
theorem original_pair_mass_le_selected (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G]
    {ε : ℝ} {M : ℕ} (hε : 0<ε) (hM : 0<M) (j : Fin M) :
    starMass d G ε 1≤starMass d G (-leftEndpoint ε M j) 1 := by
  rw [starMass_one,starMass_one,neg_neg]
  exact measureReal_mono (Iic_subset_Iic.mpr (endpoints_in_negative_band hε hM j).1)

/-- Pure finite numerical selector already proved in GaussianGGWeights. -/
abbrev NumericExclusion (ε η : ℝ) (n : ℕ) (γ C : ℝ) : Prop :=
  ∀ (a : ℝ), a∈Icc (0:ℝ) 1 → ∀ (T d : ℕ → ℝ), T 1=a →
    (∀m, 1≤m → m<n → 0≤d m) →
    (∀m, 1≤m → m<n → |T (m+1)-(((m:ℝ)+a)/((m+1:ℕ):ℝ))*T m|≤d m) →
    T n≤2*(1-γ)/ε+γ^n → a≤η+C*(∑m∈Finset.Ico 1 n,d m)

/-- Model-independent use of a proved numerical selector. Fixing this
selector before the Hilbert space gives uniform replica counts in N. -/
theorem star_exclusion_of_numeric {ε η : ℝ} (hε : 0<ε) (hε1 : ε≤1)
    (n : ℕ) (γ C : ℝ) (hγ : γ∈Ioo (0:ℝ) 1)
    (hNumeric : NumericExclusion (ε/2) η n γ C) :
    ∀ (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G],
      (∀ᵐ ω ∂d, ∀ᵐ z ∂G ω, ‖z‖≤1) →
      ∀ (M : ℕ), 0<M → ∀ (j : Fin M) (P : Polynomial ℝ) (K : ℕ), P.natDegree≤K →
      ∀ (δ : ℝ), 0≤δ → (∀r∈Icc (-1:ℝ) 1, |P.eval r-cutoff ε M j r|≤δ) →
      starMass d G ε 1≤η+C*(∑m∈Finset.Ico 1 n,
        ((∑p∈Finset.range (K+1), |P.coeff p| * powerDefect d G (-leftEndpoint ε M j) m p)+
          2*δ+2*(overlapLaw d G).real (shell ε M j))) := by
  have hhalf : 0<ε/2 := by positivity
  intro d hd G hMarkov hG M hM j P K hK δ hδ happ
  let εj := -leftEndpoint ε M j
  have he := selected_threshold_mem hε hM j
  have hεj : 0<εj := lt_of_lt_of_le hhalf he.1
  have hεj1 : εj≤1 := he.2.trans hε1
  let T : ℕ → ℝ := starMass d G εj
  let a := T 1
  have ha : a∈Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  let errors : ℕ → ℝ := fun m =>
    (∑p∈Finset.range (K+1), |P.coeff p| * powerDefect d G εj m p)+
      2*δ+2*(overlapLaw d G).real (shell ε M j)
  have herr0 (m : ℕ) : 0≤errors m := by
    dsimp [errors]
    have hs : 0≤∑p∈Finset.range (K+1), |P.coeff p| * powerDefect d G εj m p :=
      Finset.sum_nonneg fun p hp => mul_nonneg (abs_nonneg _) (powerDefect_nonneg _ _ _ _ _)
    have hm : 0≤(overlapLaw d G).real (shell ε M j) := measureReal_nonneg
    positivity
  have hGG (m : ℕ) : |T (m+1)-(((m:ℝ)+a)/((m+1:ℕ):ℝ))*T m|≤errors m := by
    simpa only [T,a,Nat.cast_add,Nat.cast_one] using
      star_recursion_le_powerDefects d G hG m hε hM j P hK hδ happ
  have hgeom : T n≤2*(1-γ)/(ε/2)+γ^n := by
    have hs := starMass_le_geometric d G hG hεj hεj1 hγ.1 hγ.2 n
    have hdiv : 2*(1-γ)/εj≤2*(1-γ)/(ε/2) :=
      div_le_div_of_nonneg_left (by nlinarith [hγ.2]) hhalf he.1
    exact hs.trans (add_le_add hdiv (le_refl _))
  have ht := hNumeric a ha T errors rfl (fun m hm hmn => herr0 m) (fun m hm hmn => hGG m) hgeom
  have ht' : starMass d G (-leftEndpoint ε M j) 1≤η+C*(∑m∈Finset.Ico 1 n,
        ((∑p∈Finset.range (K+1), |P.coeff p| * powerDefect d G (-leftEndpoint ε M j) m p)+
          2*δ+2*(overlapLaw d G).real (shell ε M j))) := by
    simpa only [a,T,εj,errors] using ht
  exact (original_pair_mass_le_selected d G hε hM j).trans ht'

/-- A finite number of actual power GG tests forces the original pair
mass small. Constants are obtained solely from ε and η. -/
theorem exists_finite_star_exclusion {ε η : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ n : ℕ, ∃ C : ℝ, 2≤n ∧ 0<C ∧
      ∀ (d : Measure Ω) [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G],
      (∀ᵐ ω ∂d, ∀ᵐ z ∂G ω, ‖z‖≤1) →
      ∀ (M : ℕ), 0<M → ∀ (j : Fin M) (P : Polynomial ℝ) (K : ℕ), P.natDegree≤K →
      ∀ (δ : ℝ), 0≤δ → (∀r∈Icc (-1:ℝ) 1, |P.eval r-cutoff ε M j r|≤δ) →
      starMass d G ε 1≤η+C*(∑m∈Finset.Ico 1 n,
        ((∑p∈Finset.range (K+1), |P.coeff p| * powerDefect d G (-leftEndpoint ε M j) m p)+
          2*δ+2*(overlapLaw d G).real (shell ε M j))) := by
  have hhalf : 0<ε/2 := by positivity
  obtain ⟨n,γ,C,hn,hγ,hC,hNumeric⟩ := GaussianGGWeights.exists_finite_exclusion hhalf hη
  exact ⟨n,C,hn,hC,star_exclusion_of_numeric hε hε1 n γ C hγ hNumeric⟩

end SlowEquilibration.GaussianGGEnsemble
