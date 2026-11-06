theory DCX_c30_065
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1040: "dc_sub dc_b30 1040"
  by (dc_eval dc_c30_1040)

lemma dc_c30_1041: "dc_sub dc_b30 1041"
  by (dc_eval dc_c30_1041)

lemma dc_c30_1042: "dc_sub dc_b30 1042"
  by (dc_eval dc_c30_1042)

lemma dc_c30_1043: "dc_sub dc_b30 1043"
  by (dc_eval dc_c30_1043)

lemma dc_c30_1044: "dc_sub dc_b30 1044"
  by (dc_eval dc_c30_1044)

lemma dc_c30_1045: "dc_sub dc_b30 1045"
  by (dc_eval dc_c30_1045)

lemma dc_c30_1046: "dc_sub dc_b30 1046"
  by (dc_eval dc_c30_1046)

lemma dc_c30_1047: "dc_sub dc_b30 1047"
  by (dc_eval dc_c30_1047)

lemma dc_c30_1048: "dc_sub dc_b30 1048"
  by (dc_eval dc_c30_1048)

lemma dc_c30_1049: "dc_sub dc_b30 1049"
  by (dc_eval dc_c30_1049)

lemma dc_c30_1050: "dc_sub dc_b30 1050"
  by (dc_eval dc_c30_1050)

lemma dc_c30_1051: "dc_sub dc_b30 1051"
  by (dc_eval dc_c30_1051)

lemma dc_c30_1052: "dc_sub dc_b30 1052"
  by (dc_eval dc_c30_1052)

lemma dc_c30_1053: "dc_sub dc_b30 1053"
  by (dc_eval dc_c30_1053)

lemma dc_c30_1054: "dc_sub dc_b30 1054"
  by (dc_eval dc_c30_1054)

lemma dc_c30_1055: "dc_sub dc_b30 1055"
  by (dc_eval dc_c30_1055)

lemma upt_c30_065: "[1040..<1056] = [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]"
  by (simp add: upt_rec)

lemma sec_c30_065: "\<forall>j\<in>{16 * 65..<16 * 65 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 65..<16 * 65 + 16}"
  then have "j \<in> set [1040..<1056]" unfolding set_upt by simp
  then have "j \<in> set [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]" unfolding upt_c30_065 .
  then show "dc_sub dc_b30 j" using dc_c30_1040 dc_c30_1041 dc_c30_1042 dc_c30_1043 dc_c30_1044 dc_c30_1045 dc_c30_1046 dc_c30_1047 dc_c30_1048 dc_c30_1049 dc_c30_1050 dc_c30_1051 dc_c30_1052 dc_c30_1053 dc_c30_1054 dc_c30_1055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
