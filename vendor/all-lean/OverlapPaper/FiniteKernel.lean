module
public import FourPapersCommon.MixtureAnalysis
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-! The actual covariance kernel of a countable even mixture preserves Gram positivity. -/
noncomputable section
open Set Filter Matrix
open scoped Topology Matrix
namespace OverlapPaper

def entrywisePower {ι : Type*} (A : Matrix ι ι ℝ) (p : ℕ) : Matrix ι ι ℝ :=
  Matrix.of (fun i j=>A i j^p)

def mixtureKernel {ι : Type*} (ξ : FourPapersCommon.AdmissibleEvenMixture)
    (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := Matrix.of (fun i j=>ξ.value (A i j))

theorem entrywise_power_posSemidef {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (p : ℕ) :
    (entrywisePower A p).PosSemidef := by
  induction p with
  | zero =>
      have he : entrywisePower A 0=Matrix.vecMulVec (fun _ : ι=>(1:ℝ))
          (star (fun _ : ι=>(1:ℝ))) := by ext i j; simp [entrywisePower,Matrix.vecMulVec]
      rw [he]
      exact Matrix.posSemidef_vecMulVec_self_star _
  | succ p ih =>
      have he : entrywisePower A (p+1)=entrywisePower A p⊙A := by
        ext i j
        simp [entrywisePower,Matrix.hadamard_apply,pow_succ]
      rw [he]
      exact ih.hadamard hA

theorem mixture_kernel_posSemidef {ι : Type*} [Fintype ι]
    (ξ : FourPapersCommon.AdmissibleEvenMixture) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hbound : ∀i j, |A i j|≤1) :
    (mixtureKernel ξ A).PosSemidef := by
  classical
  let M : ℕ→Matrix ι ι ℝ := fun p=>ξ.coefficient p • entrywisePower A p
  have hM : ∀p,(M p).PosSemidef := fun p=>
    (entrywise_power_posSemidef hA p).smul (ξ.nonneg p)
  have hlim : Tendsto (fun n=>∑p∈Finset.range n,M p) atTop
      (𝓝 (mixtureKernel ξ A)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa [M,entrywisePower,mixtureKernel,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
      FourPapersCommon.AdmissibleEvenMixture.value] using
      (ξ.summable_value (hbound i j)).hasSum.tendsto_sum_nat
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hlim
    (Filter.Eventually.of_forall (fun n=>Matrix.posSemidef_sum _ (fun p _=>hM p)))

end OverlapPaper
