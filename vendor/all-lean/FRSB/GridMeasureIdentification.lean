module
public import FRSB.CDFMeasureExt
public import Paper.ParisiPDEFormula

@[expose] public section

/-! The actual finite RSB grid scheme represents the actual rounded measure. -/
noncomputable section
open Set MeasureTheory
namespace FRSB

theorem parisiSchemeMeasure_grid_eq (μ : Paper.ParisiMeasure) (n : ℕ) :
    Paper.parisiSchemeMeasure (Paper.parisiGridRSBScheme μ n) = Paper.parisiGridMeasure μ n := by
  apply eq_of_parisiCDF_ae_eq_on
  filter_upwards [ae_restrict_mem measurableSet_Ioc, (ae_restrict_of_ae (volume.ae_ne (1:ℝ)))] with t ht ht1
  obtain ⟨p,hp0,hp,hcell,_⟩ := Paper.exists_parisiGrid_right_cell μ n ⟨ht.1.le,lt_of_le_of_ne ht.2 ht1⟩
  rw [Paper.parisiCDF_scheme_cell (Paper.parisiGridRSBScheme μ n) (by omega) hcell,
    Paper.parisiCDF_grid_eq_scheme_mass μ n p hp0 hp hcell]

/-- Every genuine grid gradient equals the constructed gradient of its rounded law. -/
theorem parisiGradient_grid_eq_finite (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (n : ℕ) :
    Paper.parisiGradient β (Paper.parisiGridMeasure μ n) =
      Paper.parisiFiniteGradient (Paper.parisiGridRSBScheme μ n) β := by
  rw [← parisiSchemeMeasure_grid_eq μ n]
  exact Paper.parisiSchemeGradient_eq_actual _ β hβ

end FRSB
