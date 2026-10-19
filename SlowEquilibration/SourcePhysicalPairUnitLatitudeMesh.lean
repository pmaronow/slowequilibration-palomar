-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairLatitudeReconstruction

/-! A finite radial grid, chosen before dimension, controls the original
Hamiltonian on every sphere point of the entire positive overlap band. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel SphericalGaussianJet SphericalForm IntrinsicHessianLaw
open SphericalCriticalLatitude PureTensorJetBounds Set Metric
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma sourceUnitLatitudeMap_eq_latitudeMap {n:ℕ} (hn:1 ≤ n) (u:Vector (n+1))
    (e:Vector n→ₗᵢ[ℝ]Vector (n+1)) {r:ℝ} (hr:|r| ≤ 1) (x:Vector n) :
    sourceUnitLatitudeMap u e r x=latitudeMap u e r (Real.sqrt (n:ℝ) • x):=by
  have hn':(0:ℝ)<n:=Nat.cast_pos.mpr (by omega)
  have hsq:0 ≤ 1-r^2:=by nlinarith [abs_le.mp hr]
  have he:Real.sqrt (((n+1:ℕ):ℝ)/(n:ℝ)*(1-r^2))*Real.sqrt (n:ℝ)=
      Real.sqrt ((n+1:ℕ)*(1-r^2)):=by
    rw [←Real.sqrt_mul (mul_nonneg (by positivity) hsq)]
    congr 1
    field_simp
  unfold sourceUnitLatitudeMap latitudeMap
  rw [map_smul,smul_smul,he]

theorem source_ordered_unitLatitude_field_modulus {n P:ℕ} (hn:1 ≤ n)
    (c:Degree P→ℝ) {K:ℝ} (hK:0 ≤ K) (J:Disorder (n+1) P)
    (hJ:J ∈ sourcePosteriorOrderedRegularity K) (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (e:Vector n→ₗᵢ[ℝ]Vector (n+1)) (he:∀ v,inner ℝ (e v) u=0)
    {q r:ℝ} (hq:|q| ≤ 1) (hr:|r| ≤ 1) (x:UnitSphere n) :
    |field c J (sourceUnitLatitudeMap u e q x)-field c J (sourceUnitLatitudeMap u e r x)| ≤
      2*sourcePosteriorDerivativeConstant c K*(n+1:ℕ)*Real.sqrt |q-r|:=by
  have hx:‖Real.sqrt (n:ℝ) • (x:Vector n)‖^2=(n:ℝ):=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),unit_norm x,mul_one,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [sourceUnitLatitudeMap_eq_latitudeMap hn u e hq,sourceUnitLatitudeMap_eq_latitudeMap hn u e hr]
  exact source_ordered_latitude_field_modulus hn c K hK J hJ u hu e he hq hr _ hx

def sourceUnitLatitudeMaximum {n P:ℕ} (c:Degree P→ℝ) (u:Vector (n+1))
    (e:Vector n→ₗᵢ[ℝ]Vector (n+1)) (r:ℝ) (J:Disorder (n+1) P):ℝ:=
  ⨆ x:UnitSphere n,field c J (sourceUnitLatitudeMap u e r x)

lemma sourceUnitLatitudeMaximum_point_le {n P:ℕ} (c:Degree P→ℝ) (u:Vector (n+1))
    (e:Vector n→ₗᵢ[ℝ]Vector (n+1)) (r:ℝ) (J:Disorder (n+1) P) (x:UnitSphere n) :
    field c J (sourceUnitLatitudeMap u e r x) ≤ sourceUnitLatitudeMaximum c u e r J:=by
  have hc:Continuous (fun x:UnitSphere n=>field c J (sourceUnitLatitudeMap u e r x)):=
    (field_contDiff c J).continuous.comp
      ((sourceUnitLatitudeMap_continuous u e r).comp continuous_subtype_val)
  exact le_ciSup (isCompact_range hc).bddAbove x

lemma source_radial_mesh_exists {a b L s:ℝ} (hab:a ≤ b) (hL:0<L) (hs:0<s) :
    ∃ k:ℕ,1 ≤ k ∧ 2*L*Real.sqrt ((b-a)/(k:ℝ)) ≤ s:=by
  let δ:=(s/(2*L))^2
  have hδ:0<δ:=sq_pos_of_pos (div_pos hs (mul_pos (by norm_num) hL))
  obtain ⟨k,hk⟩:=exists_nat_gt ((b-a)/δ+1)
  have hk':0<(k:ℝ):=lt_trans (by positivity) hk
  have hkN:1 ≤ k:=by exact_mod_cast hk'
  have hb:(b-a)/(k:ℝ) ≤ δ:=by
    apply (div_le_iff₀ hk').mpr
    have ht:(b-a)/δ < (k:ℝ):=lt_trans (by linarith) hk
    have hh:=(div_lt_iff₀ hδ).mp ht
    nlinarith
  have hh:Real.sqrt ((b-a)/(k:ℝ)) ≤ s/(2*L):=by
    have ht:=Real.sqrt_le_sqrt hb
    rw [Real.sqrt_sq (div_nonneg hs.le (by positivity))] at ht
    exact ht
  refine ⟨k,hkN,?_⟩
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)

theorem sourceOverlapBandHeight_of_radial_mesh {n P k:ℕ} (hn:1 ≤ n) (hk:1 ≤ k)
    (c:Degree P→ℝ) {K ε η s H:ℝ} (hK:0 ≤ K) (hε:0<ε) (hη:0<η)
    (hab:ε ≤ 1-η) (hmesh:2*sourcePosteriorDerivativeConstant c K*
      Real.sqrt (((1-η)-ε)/(k:ℝ)) ≤ s)
    (J:Disorder (n+1) P) (hJ:J ∈ sourcePosteriorOrderedRegularity K)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ))
    (hgrid:∀ i:Fin (k+1),sourceUnitLatitudeMaximum c u (sourceLatitudeIsometry u hu)
      (latitudeMeshPoint k ε (1-η) i) J ≤ (n+1:ℕ)*H) :
    sourceOverlapBandHeight c ε η ((n+1:ℕ)*(H+s)) J u:=by
  rw [sourceOverlapBandHeight_unit_iff c hε hη _ J u hu]
  intro r hr x
  obtain ⟨i,hi⟩:=latitudeMeshPoint_covers hk hab hr
  have him:=latitudeMeshPoint_mem hk hab i
  have hrabs:|r| ≤ 1:=abs_le.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hiabs:|latitudeMeshPoint k ε (1-η) i| ≤ 1:=abs_le.mpr ⟨by linarith [him.1],by linarith [him.2]⟩
  have hm:=source_ordered_unitLatitude_field_modulus hn c hK J hJ u hu _
    (sourceLatitudeIsometry_orthogonal u hu) hrabs hiabs x
  have hL:=sourcePosteriorDerivativeConstant_pos c hK
  have hd:|field c J (sourceUnitLatitudeMap u (sourceLatitudeIsometry u hu) r x)-
      field c J (sourceUnitLatitudeMap u (sourceLatitudeIsometry u hu) (latitudeMeshPoint k ε (1-η) i) x)| ≤
      (n+1:ℕ)*s:=by
    apply hm.trans
    calc
      _ ≤ 2*sourcePosteriorDerivativeConstant c K*(n+1:ℕ)*Real.sqrt (((1-η)-ε)/(k:ℝ)):=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi) (by positivity)
      _ = (n+1:ℕ)*(2*sourcePosteriorDerivativeConstant c K*Real.sqrt (((1-η)-ε)/(k:ℝ))):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hmesh (by positivity)
  have hg:field c J (sourceUnitLatitudeMap u (sourceLatitudeIsometry u hu) (latitudeMeshPoint k ε (1-η) i) x) ≤
      (n+1:ℕ)*H:=(sourceUnitLatitudeMaximum_point_le _ _ _ _ _ x).trans (hgrid i)
  nlinarith [le_abs_self (field c J (sourceUnitLatitudeMap u (sourceLatitudeIsometry u hu) r x)-
    field c J (sourceUnitLatitudeMap u (sourceLatitudeIsometry u hu) (latitudeMeshPoint k ε (1-η) i) x))]

theorem sourceBandHeight_failure_subset_mesh {n P k:ℕ} (hn:1 ≤ n) (hk:1 ≤ k)
    (c:Degree P→ℝ) {K ε η s H:ℝ} (hK:0 ≤ K) (hε:0<ε) (hη:0<η)
    (hab:ε ≤ 1-η) (hmesh:2*sourcePosteriorDerivativeConstant c K*
      Real.sqrt (((1-η)-ε)/(k:ℝ)) ≤ s)
    (u:Vector (n+1)) (hu:‖u‖^2=(n+1:ℕ)) :
    {J:Disorder (n+1) P|¬sourceOverlapBandHeight c ε η ((n+1:ℕ)*(H+s)) J u} ⊆
      (sourcePosteriorOrderedRegularity (N:=n+1) (P:=P) K)ᶜ ∪
        ⋃ i:Fin (k+1),{J| (n+1:ℕ)*H<sourceUnitLatitudeMaximum c u (sourceLatitudeIsometry u hu)
          (latitudeMeshPoint k ε (1-η) i) J}:=by
  classical
  intro J hbad
  by_cases hgood:J ∈ sourcePosteriorOrderedRegularity K
  · apply Or.inr
    by_contra hnone
    apply hbad
    apply sourceOverlapBandHeight_of_radial_mesh hn hk c hK hε hη hab hmesh J hgood u hu
    intro i
    have hi:¬(n+1:ℕ)*H<sourceUnitLatitudeMaximum c u (sourceLatitudeIsometry u hu)
        (latitudeMeshPoint k ε (1-η) i) J:=by
      intro hlt
      exact hnone (Set.mem_iUnion.mpr ⟨i,hlt⟩)
    exact le_of_not_gt hi
  · exact Or.inl hgood

end
end SlowEquilibration.PairConditionalDeterminantMoments
