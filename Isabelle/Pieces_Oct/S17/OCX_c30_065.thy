theory OCX_c30_065
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1040: "oc_sub oc_b30 1040"
  by (oc_eval oc_c30_1040)

lemma oc_c30_1041: "oc_sub oc_b30 1041"
  by (oc_eval oc_c30_1041)

lemma oc_c30_1042: "oc_sub oc_b30 1042"
  by (oc_eval oc_c30_1042)

lemma oc_c30_1043: "oc_sub oc_b30 1043"
  by (oc_eval oc_c30_1043)

lemma oc_c30_1044: "oc_sub oc_b30 1044"
  by (oc_eval oc_c30_1044)

lemma oc_c30_1045: "oc_sub oc_b30 1045"
  by (oc_eval oc_c30_1045)

lemma oc_c30_1046: "oc_sub oc_b30 1046"
  by (oc_eval oc_c30_1046)

lemma oc_c30_1047: "oc_sub oc_b30 1047"
  by (oc_eval oc_c30_1047)

lemma oc_c30_1048: "oc_sub oc_b30 1048"
  by (oc_eval oc_c30_1048)

lemma oc_c30_1049: "oc_sub oc_b30 1049"
  by (oc_eval oc_c30_1049)

lemma oc_c30_1050: "oc_sub oc_b30 1050"
  by (oc_eval oc_c30_1050)

lemma oc_c30_1051: "oc_sub oc_b30 1051"
  by (oc_eval oc_c30_1051)

lemma oc_c30_1052: "oc_sub oc_b30 1052"
  by (oc_eval oc_c30_1052)

lemma oc_c30_1053: "oc_sub oc_b30 1053"
  by (oc_eval oc_c30_1053)

lemma oc_c30_1054: "oc_sub oc_b30 1054"
  by (oc_eval oc_c30_1054)

lemma oc_c30_1055: "oc_sub oc_b30 1055"
  by (oc_eval oc_c30_1055)

lemma upt_c30_065: "[1040..<1056] = [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]"
  by (simp add: upt_rec)

lemma sec_c30_065: "\<forall>j\<in>{16 * 65..<16 * 65 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 65..<16 * 65 + 16}"
  then have "j \<in> set [1040..<1056]" unfolding set_upt by simp
  then have "j \<in> set [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]" unfolding upt_c30_065 .
  then show "oc_sub oc_b30 j" using oc_c30_1040 oc_c30_1041 oc_c30_1042 oc_c30_1043 oc_c30_1044 oc_c30_1045 oc_c30_1046 oc_c30_1047 oc_c30_1048 oc_c30_1049 oc_c30_1050 oc_c30_1051 oc_c30_1052 oc_c30_1053 oc_c30_1054 oc_c30_1055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
