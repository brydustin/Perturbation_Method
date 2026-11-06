theory GDCX_nc_190
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3040: "gdc_sub None 3040"
  by (gdc_eval gdc_nc_3040)

lemma gdc_nc_3041: "gdc_sub None 3041"
  by (gdc_eval gdc_nc_3041)

lemma gdc_nc_3042: "gdc_sub None 3042"
  by (gdc_eval gdc_nc_3042)

lemma gdc_nc_3043: "gdc_sub None 3043"
  by (gdc_eval gdc_nc_3043)

lemma gdc_nc_3044: "gdc_sub None 3044"
  by (gdc_eval gdc_nc_3044)

lemma gdc_nc_3045: "gdc_sub None 3045"
  by (gdc_eval gdc_nc_3045)

lemma gdc_nc_3046: "gdc_sub None 3046"
  by (gdc_eval gdc_nc_3046)

lemma gdc_nc_3047: "gdc_sub None 3047"
  by (gdc_eval gdc_nc_3047)

lemma gdc_nc_3048: "gdc_sub None 3048"
  by (gdc_eval gdc_nc_3048)

lemma gdc_nc_3049: "gdc_sub None 3049"
  by (gdc_eval gdc_nc_3049)

lemma gdc_nc_3050: "gdc_sub None 3050"
  by (gdc_eval gdc_nc_3050)

lemma gdc_nc_3051: "gdc_sub None 3051"
  by (gdc_eval gdc_nc_3051)

lemma gdc_nc_3052: "gdc_sub None 3052"
  by (gdc_eval gdc_nc_3052)

lemma gdc_nc_3053: "gdc_sub None 3053"
  by (gdc_eval gdc_nc_3053)

lemma gdc_nc_3054: "gdc_sub None 3054"
  by (gdc_eval gdc_nc_3054)

lemma gdc_nc_3055: "gdc_sub None 3055"
  by (gdc_eval gdc_nc_3055)

lemma gupt_nc_190: "[3040..<3056] = [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]"
  by (simp add: upt_rec)

lemma gsec_nc_190: "\<forall>j\<in>{16 * 190..<16 * 190 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 190..<16 * 190 + 16}"
  then have "j \<in> set [3040..<3056]" unfolding set_upt by simp
  then have "j \<in> set [3040, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055]" unfolding gupt_nc_190 .
  then show "gdc_sub None j" using gdc_nc_3040 gdc_nc_3041 gdc_nc_3042 gdc_nc_3043 gdc_nc_3044 gdc_nc_3045 gdc_nc_3046 gdc_nc_3047 gdc_nc_3048 gdc_nc_3049 gdc_nc_3050 gdc_nc_3051 gdc_nc_3052 gdc_nc_3053 gdc_nc_3054 gdc_nc_3055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
