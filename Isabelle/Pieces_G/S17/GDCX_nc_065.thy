theory GDCX_nc_065
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1040: "gdc_sub None 1040"
  by (gdc_eval gdc_nc_1040)

lemma gdc_nc_1041: "gdc_sub None 1041"
  by (gdc_eval gdc_nc_1041)

lemma gdc_nc_1042: "gdc_sub None 1042"
  by (gdc_eval gdc_nc_1042)

lemma gdc_nc_1043: "gdc_sub None 1043"
  by (gdc_eval gdc_nc_1043)

lemma gdc_nc_1044: "gdc_sub None 1044"
  by (gdc_eval gdc_nc_1044)

lemma gdc_nc_1045: "gdc_sub None 1045"
  by (gdc_eval gdc_nc_1045)

lemma gdc_nc_1046: "gdc_sub None 1046"
  by (gdc_eval gdc_nc_1046)

lemma gdc_nc_1047: "gdc_sub None 1047"
  by (gdc_eval gdc_nc_1047)

lemma gdc_nc_1048: "gdc_sub None 1048"
  by (gdc_eval gdc_nc_1048)

lemma gdc_nc_1049: "gdc_sub None 1049"
  by (gdc_eval gdc_nc_1049)

lemma gdc_nc_1050: "gdc_sub None 1050"
  by (gdc_eval gdc_nc_1050)

lemma gdc_nc_1051: "gdc_sub None 1051"
  by (gdc_eval gdc_nc_1051)

lemma gdc_nc_1052: "gdc_sub None 1052"
  by (gdc_eval gdc_nc_1052)

lemma gdc_nc_1053: "gdc_sub None 1053"
  by (gdc_eval gdc_nc_1053)

lemma gdc_nc_1054: "gdc_sub None 1054"
  by (gdc_eval gdc_nc_1054)

lemma gdc_nc_1055: "gdc_sub None 1055"
  by (gdc_eval gdc_nc_1055)

lemma gupt_nc_065: "[1040..<1056] = [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]"
  by (simp add: upt_rec)

lemma gsec_nc_065: "\<forall>j\<in>{16 * 65..<16 * 65 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 65..<16 * 65 + 16}"
  then have "j \<in> set [1040..<1056]" unfolding set_upt by simp
  then have "j \<in> set [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]" unfolding gupt_nc_065 .
  then show "gdc_sub None j" using gdc_nc_1040 gdc_nc_1041 gdc_nc_1042 gdc_nc_1043 gdc_nc_1044 gdc_nc_1045 gdc_nc_1046 gdc_nc_1047 gdc_nc_1048 gdc_nc_1049 gdc_nc_1050 gdc_nc_1051 gdc_nc_1052 gdc_nc_1053 gdc_nc_1054 gdc_nc_1055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
