theory DCX_nc_065
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1040: "dc_sub None 1040"
  by (dc_eval dc_nc_1040)

lemma dc_nc_1041: "dc_sub None 1041"
  by (dc_eval dc_nc_1041)

lemma dc_nc_1042: "dc_sub None 1042"
  by (dc_eval dc_nc_1042)

lemma dc_nc_1043: "dc_sub None 1043"
  by (dc_eval dc_nc_1043)

lemma dc_nc_1044: "dc_sub None 1044"
  by (dc_eval dc_nc_1044)

lemma dc_nc_1045: "dc_sub None 1045"
  by (dc_eval dc_nc_1045)

lemma dc_nc_1046: "dc_sub None 1046"
  by (dc_eval dc_nc_1046)

lemma dc_nc_1047: "dc_sub None 1047"
  by (dc_eval dc_nc_1047)

lemma dc_nc_1048: "dc_sub None 1048"
  by (dc_eval dc_nc_1048)

lemma dc_nc_1049: "dc_sub None 1049"
  by (dc_eval dc_nc_1049)

lemma dc_nc_1050: "dc_sub None 1050"
  by (dc_eval dc_nc_1050)

lemma dc_nc_1051: "dc_sub None 1051"
  by (dc_eval dc_nc_1051)

lemma dc_nc_1052: "dc_sub None 1052"
  by (dc_eval dc_nc_1052)

lemma dc_nc_1053: "dc_sub None 1053"
  by (dc_eval dc_nc_1053)

lemma dc_nc_1054: "dc_sub None 1054"
  by (dc_eval dc_nc_1054)

lemma dc_nc_1055: "dc_sub None 1055"
  by (dc_eval dc_nc_1055)

lemma upt_nc_065: "[1040..<1056] = [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]"
  by (simp add: upt_rec)

lemma sec_nc_065: "\<forall>j\<in>{16 * 65..<16 * 65 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 65..<16 * 65 + 16}"
  then have "j \<in> set [1040..<1056]" unfolding set_upt by simp
  then have "j \<in> set [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]" unfolding upt_nc_065 .
  then show "dc_sub None j" using dc_nc_1040 dc_nc_1041 dc_nc_1042 dc_nc_1043 dc_nc_1044 dc_nc_1045 dc_nc_1046 dc_nc_1047 dc_nc_1048 dc_nc_1049 dc_nc_1050 dc_nc_1051 dc_nc_1052 dc_nc_1053 dc_nc_1054 dc_nc_1055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
