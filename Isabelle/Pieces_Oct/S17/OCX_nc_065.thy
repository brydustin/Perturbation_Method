theory OCX_nc_065
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1040: "oc_sub None 1040"
  by (oc_eval oc_nc_1040)

lemma oc_nc_1041: "oc_sub None 1041"
  by (oc_eval oc_nc_1041)

lemma oc_nc_1042: "oc_sub None 1042"
  by (oc_eval oc_nc_1042)

lemma oc_nc_1043: "oc_sub None 1043"
  by (oc_eval oc_nc_1043)

lemma oc_nc_1044: "oc_sub None 1044"
  by (oc_eval oc_nc_1044)

lemma oc_nc_1045: "oc_sub None 1045"
  by (oc_eval oc_nc_1045)

lemma oc_nc_1046: "oc_sub None 1046"
  by (oc_eval oc_nc_1046)

lemma oc_nc_1047: "oc_sub None 1047"
  by (oc_eval oc_nc_1047)

lemma oc_nc_1048: "oc_sub None 1048"
  by (oc_eval oc_nc_1048)

lemma oc_nc_1049: "oc_sub None 1049"
  by (oc_eval oc_nc_1049)

lemma oc_nc_1050: "oc_sub None 1050"
  by (oc_eval oc_nc_1050)

lemma oc_nc_1051: "oc_sub None 1051"
  by (oc_eval oc_nc_1051)

lemma oc_nc_1052: "oc_sub None 1052"
  by (oc_eval oc_nc_1052)

lemma oc_nc_1053: "oc_sub None 1053"
  by (oc_eval oc_nc_1053)

lemma oc_nc_1054: "oc_sub None 1054"
  by (oc_eval oc_nc_1054)

lemma oc_nc_1055: "oc_sub None 1055"
  by (oc_eval oc_nc_1055)

lemma upt_nc_065: "[1040..<1056] = [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]"
  by (simp add: upt_rec)

lemma sec_nc_065: "\<forall>j\<in>{16 * 65..<16 * 65 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 65..<16 * 65 + 16}"
  then have "j \<in> set [1040..<1056]" unfolding set_upt by simp
  then have "j \<in> set [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]" unfolding upt_nc_065 .
  then show "oc_sub None j" using oc_nc_1040 oc_nc_1041 oc_nc_1042 oc_nc_1043 oc_nc_1044 oc_nc_1045 oc_nc_1046 oc_nc_1047 oc_nc_1048 oc_nc_1049 oc_nc_1050 oc_nc_1051 oc_nc_1052 oc_nc_1053 oc_nc_1054 oc_nc_1055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
