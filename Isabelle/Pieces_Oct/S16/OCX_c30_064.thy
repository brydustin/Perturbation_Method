theory OCX_c30_064
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1024: "oc_sub oc_b30 1024"
  by (oc_eval oc_c30_1024)

lemma oc_c30_1025: "oc_sub oc_b30 1025"
  by (oc_eval oc_c30_1025)

lemma oc_c30_1026: "oc_sub oc_b30 1026"
  by (oc_eval oc_c30_1026)

lemma oc_c30_1027: "oc_sub oc_b30 1027"
  by (oc_eval oc_c30_1027)

lemma oc_c30_1028: "oc_sub oc_b30 1028"
  by (oc_eval oc_c30_1028)

lemma oc_c30_1029: "oc_sub oc_b30 1029"
  by (oc_eval oc_c30_1029)

lemma oc_c30_1030: "oc_sub oc_b30 1030"
  by (oc_eval oc_c30_1030)

lemma oc_c30_1031: "oc_sub oc_b30 1031"
  by (oc_eval oc_c30_1031)

lemma oc_c30_1032: "oc_sub oc_b30 1032"
  by (oc_eval oc_c30_1032)

lemma oc_c30_1033: "oc_sub oc_b30 1033"
  by (oc_eval oc_c30_1033)

lemma oc_c30_1034: "oc_sub oc_b30 1034"
  by (oc_eval oc_c30_1034)

lemma oc_c30_1035: "oc_sub oc_b30 1035"
  by (oc_eval oc_c30_1035)

lemma oc_c30_1036: "oc_sub oc_b30 1036"
  by (oc_eval oc_c30_1036)

lemma oc_c30_1037: "oc_sub oc_b30 1037"
  by (oc_eval oc_c30_1037)

lemma oc_c30_1038: "oc_sub oc_b30 1038"
  by (oc_eval oc_c30_1038)

lemma oc_c30_1039: "oc_sub oc_b30 1039"
  by (oc_eval oc_c30_1039)

lemma upt_c30_064: "[1024..<1040] = [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]"
  by (simp add: upt_rec)

lemma sec_c30_064: "\<forall>j\<in>{16 * 64..<16 * 64 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 64..<16 * 64 + 16}"
  then have "j \<in> set [1024..<1040]" unfolding set_upt by simp
  then have "j \<in> set [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]" unfolding upt_c30_064 .
  then show "oc_sub oc_b30 j" using oc_c30_1024 oc_c30_1025 oc_c30_1026 oc_c30_1027 oc_c30_1028 oc_c30_1029 oc_c30_1030 oc_c30_1031 oc_c30_1032 oc_c30_1033 oc_c30_1034 oc_c30_1035 oc_c30_1036 oc_c30_1037 oc_c30_1038 oc_c30_1039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
