theory GDCX_nc_189
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3024: "gdc_sub None 3024"
  by (gdc_eval gdc_nc_3024)

lemma gdc_nc_3025: "gdc_sub None 3025"
  by (gdc_eval gdc_nc_3025)

lemma gdc_nc_3026: "gdc_sub None 3026"
  by (gdc_eval gdc_nc_3026)

lemma gdc_nc_3027: "gdc_sub None 3027"
  by (gdc_eval gdc_nc_3027)

lemma gdc_nc_3028: "gdc_sub None 3028"
  by (gdc_eval gdc_nc_3028)

lemma gdc_nc_3029: "gdc_sub None 3029"
  by (gdc_eval gdc_nc_3029)

lemma gdc_nc_3030: "gdc_sub None 3030"
  by (gdc_eval gdc_nc_3030)

lemma gdc_nc_3031: "gdc_sub None 3031"
  by (gdc_eval gdc_nc_3031)

lemma gdc_nc_3032: "gdc_sub None 3032"
  by (gdc_eval gdc_nc_3032)

lemma gdc_nc_3033: "gdc_sub None 3033"
  by (gdc_eval gdc_nc_3033)

lemma gdc_nc_3034: "gdc_sub None 3034"
  by (gdc_eval gdc_nc_3034)

lemma gdc_nc_3035: "gdc_sub None 3035"
  by (gdc_eval gdc_nc_3035)

lemma gdc_nc_3036: "gdc_sub None 3036"
  by (gdc_eval gdc_nc_3036)

lemma gdc_nc_3037: "gdc_sub None 3037"
  by (gdc_eval gdc_nc_3037)

lemma gdc_nc_3038: "gdc_sub None 3038"
  by (gdc_eval gdc_nc_3038)

lemma gdc_nc_3039: "gdc_sub None 3039"
  by (gdc_eval gdc_nc_3039)

lemma gupt_nc_189: "[3024..<3040] = [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]"
  by (simp add: upt_rec)

lemma gsec_nc_189: "\<forall>j\<in>{16 * 189..<16 * 189 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 189..<16 * 189 + 16}"
  then have "j \<in> set [3024..<3040]" unfolding set_upt by simp
  then have "j \<in> set [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]" unfolding gupt_nc_189 .
  then show "gdc_sub None j" using gdc_nc_3024 gdc_nc_3025 gdc_nc_3026 gdc_nc_3027 gdc_nc_3028 gdc_nc_3029 gdc_nc_3030 gdc_nc_3031 gdc_nc_3032 gdc_nc_3033 gdc_nc_3034 gdc_nc_3035 gdc_nc_3036 gdc_nc_3037 gdc_nc_3038 gdc_nc_3039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
