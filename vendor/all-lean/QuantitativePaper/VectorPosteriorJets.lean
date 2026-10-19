module
public import QuantitativePaper.VectorPosteriorCoercivity
public import QuantitativePaper.BoundedPositiveJets

@[expose] public section

/-! Actual global third/fourth derivative bounds of the finite vector posterior.
The non-Gaussian correction has bounded positive-order jets; the Gaussian
quadratic has zero jets from order three onward. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 64
set_option backward.isDefEq.respectTransparency false

theorem boundedPositiveJets_vectorEuclideanHistoryPotential {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) : BoundedPositiveJets (vectorEuclideanHistoryPotential (n := n) s β t i) := by
  refine ⟨contDiff_vectorEuclideanHistoryPotential s β t i,?_⟩
  intro j hj
  obtain ⟨K,hK,hJets⟩ := exists_vectorRecursion_joint_jet_bound (n := n) s β t j (k+2-i)
  let L := vectorEuclideanStateLinear (n := n) s β t i
  refine ⟨K^j*‖L‖^j,mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (norm_nonneg _) _),fun x => ?_⟩
  rw [vectorEuclideanHistoryPotential_eq_comp]
  rw [L.iteratedFDeriv_comp_right (contDiff_vectorRecursion_joint s β t _) x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun p : VectorParameter n => vectorRecursion s β t p.1 (k+2-i) p.2) (L x)‖*
        ∏ _ : Fin j,‖L‖ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ K^j*‖L‖^j := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (hJets j hj le_rfl (L x)) (pow_nonneg (norm_nonneg _) _)

theorem boundedPositiveJets_vectorPosteriorCorrection {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (σ : Configuration n) :
    BoundedPositiveJets (vectorPosteriorCorrection (n := n) s β t a σ) := by
  rw [vectorPosteriorCorrection_eq]
  have h0 := (boundedPositiveJets_linear (vectorEuclideanTerminalLinear s β t σ)).neg
  have h1 := (boundedPositiveJets_vectorEuclideanHistoryPotential (n := n) s β t 1).const_mul (s.m 1-a)
  have hsum := boundedPositiveJets_finite_sum (Finset.range k)
    (fun i x => (s.m (i+2)-s.m (i+1))*vectorEuclideanHistoryPotential (n := n) s β t (i+2) x)
    (fun i _ => (boundedPositiveJets_vectorEuclideanHistoryPotential s β t (i+2)).const_mul _)
  exact ((h0.add h1).add hsum).add (boundedPositiveJets_const _)

theorem fderiv_standardGaussianPotential {ι : Type*} [Fintype ι] :
    fderiv ℝ (standardGaussianPotential (ι := ι))=innerSL ℝ := by
  haveI : ContinuousSMul ℝ (EuclideanSpace ℝ ι) := inferInstance
  funext y
  have hh := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_smul (1/2 : ℝ)).add_const
    ((Fintype.card ι : ℝ)*Real.log (Real.sqrt (2*Real.pi)))
  have hd : HasFDerivAt (standardGaussianPotential (ι := ι)) (innerSL ℝ y) y := by
    convert! hh using 1
    · funext w
      simp only [standardGaussianPotential,Pi.smul_apply,smul_eq_mul]
      ring
    · ext w
      simp only [smul_apply,smul_eq_mul]
      ring
  exact hd.fderiv

theorem norm_iteratedFDeriv_standardGaussianPotential_eq_zero {ι : Type*} [Fintype ι]
    {j : ℕ} (hj : 3 ≤ j) (x : EuclideanSpace ℝ ι) :
    ‖iteratedFDeriv ℝ j standardGaussianPotential x‖=0 := by
  haveI : ContinuousSMul ℝ (EuclideanSpace ℝ ι) := inferInstance
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hj
  have he : j=(m+1)+1+1 := by omega
  rw [he,←norm_iteratedFDeriv_fderiv,fderiv_standardGaussianPotential,
    ←norm_iteratedFDeriv_fderiv]
  have hf : fderiv ℝ (innerSL ℝ (E := EuclideanSpace ℝ ι))=
      fun _ => innerSL ℝ := funext fun _ => (innerSL ℝ (E := EuclideanSpace ℝ ι)).fderiv
  rw [hf,iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,norm_zero]

theorem exists_vectorPosteriorPotential_jet_bound {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (σ : Configuration n) {j : ℕ} (hj : 3 ≤ j) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ x : VectorGaussianSpace n k,
      ‖iteratedFDeriv ℝ j (vectorPosteriorPotential s β t a σ) x‖ ≤ B := by
  obtain ⟨B,hB,hBound⟩ := (boundedPositiveJets_vectorPosteriorCorrection s β t a σ).2 j (by omega)
  refine ⟨B,hB,fun x => ?_⟩
  have he : vectorPosteriorPotential (n := n) s β t a σ=
      fun y => standardGaussianPotential y+vectorPosteriorCorrection s β t a σ y := by
    funext y
    unfold vectorPosteriorCorrection
    ring
  rw [he]
  change ‖iteratedFDeriv ℝ j (standardGaussianPotential+vectorPosteriorCorrection s β t a σ) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (contDiff_standardGaussianPotential.of_le (by simp)).contDiffAt
    ((boundedPositiveJets_vectorPosteriorCorrection s β t a σ).1.of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (by
    rw [norm_iteratedFDeriv_standardGaussianPotential_eq_zero hj,zero_add]
    exact hBound x)

end QuantitativePaper
