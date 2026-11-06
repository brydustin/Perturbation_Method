theory GOCX_nc_189
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3024: "goc_sub None 3024"
  by (goc_eval goc_nc_3024)

lemma goc_nc_3025: "goc_sub None 3025"
  by (goc_eval goc_nc_3025)

lemma goc_nc_3026: "goc_sub None 3026"
  by (goc_eval goc_nc_3026)

lemma goc_nc_3027: "goc_sub None 3027"
  by (goc_eval goc_nc_3027)

lemma goc_nc_3028: "goc_sub None 3028"
  by (goc_eval goc_nc_3028)

lemma goc_nc_3029: "goc_sub None 3029"
  by (goc_eval goc_nc_3029)

lemma goc_nc_3030: "goc_sub None 3030"
  by (goc_eval goc_nc_3030)

lemma goc_nc_3031: "goc_sub None 3031"
  by (goc_eval goc_nc_3031)

lemma goc_nc_3032: "goc_sub None 3032"
  by (goc_eval goc_nc_3032)

lemma goc_nc_3033: "goc_sub None 3033"
  by (goc_eval goc_nc_3033)

lemma goc_nc_3034: "goc_sub None 3034"
  by (goc_eval goc_nc_3034)

lemma goc_nc_3035: "goc_sub None 3035"
  by (goc_eval goc_nc_3035)

lemma goc_nc_3036: "goc_sub None 3036"
  by (goc_eval goc_nc_3036)

lemma goc_nc_3037: "goc_sub None 3037"
  by (goc_eval goc_nc_3037)

lemma goc_nc_3038: "goc_sub None 3038"
  by (goc_eval goc_nc_3038)

lemma goc_nc_3039: "goc_sub None 3039"
  by (goc_eval goc_nc_3039)

lemma gupt_nc_189: "[3024..<3040] = [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]"
  by (simp add: upt_rec)

lemma gsec_nc_189: "\<forall>j\<in>{16 * 189..<16 * 189 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 189..<16 * 189 + 16}"
  then have "j \<in> set [3024..<3040]" unfolding set_upt by simp
  then have "j \<in> set [3024, 3025, 3026, 3027, 3028, 3029, 3030, 3031, 3032, 3033, 3034, 3035, 3036, 3037, 3038, 3039]" unfolding gupt_nc_189 .
  then show "goc_sub None j" using goc_nc_3024 goc_nc_3025 goc_nc_3026 goc_nc_3027 goc_nc_3028 goc_nc_3029 goc_nc_3030 goc_nc_3031 goc_nc_3032 goc_nc_3033 goc_nc_3034 goc_nc_3035 goc_nc_3036 goc_nc_3037 goc_nc_3038 goc_nc_3039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
