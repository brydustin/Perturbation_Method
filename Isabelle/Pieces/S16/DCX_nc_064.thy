theory DCX_nc_064
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1024: "dc_sub None 1024"
  by (dc_eval dc_nc_1024)

lemma dc_nc_1025: "dc_sub None 1025"
  by (dc_eval dc_nc_1025)

lemma dc_nc_1026: "dc_sub None 1026"
  by (dc_eval dc_nc_1026)

lemma dc_nc_1027: "dc_sub None 1027"
  by (dc_eval dc_nc_1027)

lemma dc_nc_1028: "dc_sub None 1028"
  by (dc_eval dc_nc_1028)

lemma dc_nc_1029: "dc_sub None 1029"
  by (dc_eval dc_nc_1029)

lemma dc_nc_1030: "dc_sub None 1030"
  by (dc_eval dc_nc_1030)

lemma dc_nc_1031: "dc_sub None 1031"
  by (dc_eval dc_nc_1031)

lemma dc_nc_1032: "dc_sub None 1032"
  by (dc_eval dc_nc_1032)

lemma dc_nc_1033: "dc_sub None 1033"
  by (dc_eval dc_nc_1033)

lemma dc_nc_1034: "dc_sub None 1034"
  by (dc_eval dc_nc_1034)

lemma dc_nc_1035: "dc_sub None 1035"
  by (dc_eval dc_nc_1035)

lemma dc_nc_1036: "dc_sub None 1036"
  by (dc_eval dc_nc_1036)

lemma dc_nc_1037: "dc_sub None 1037"
  by (dc_eval dc_nc_1037)

lemma dc_nc_1038: "dc_sub None 1038"
  by (dc_eval dc_nc_1038)

lemma dc_nc_1039: "dc_sub None 1039"
  by (dc_eval dc_nc_1039)

lemma upt_nc_064: "[1024..<1040] = [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]"
  by (simp add: upt_rec)

lemma sec_nc_064: "\<forall>j\<in>{16 * 64..<16 * 64 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 64..<16 * 64 + 16}"
  then have "j \<in> set [1024..<1040]" unfolding set_upt by simp
  then have "j \<in> set [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]" unfolding upt_nc_064 .
  then show "dc_sub None j" using dc_nc_1024 dc_nc_1025 dc_nc_1026 dc_nc_1027 dc_nc_1028 dc_nc_1029 dc_nc_1030 dc_nc_1031 dc_nc_1032 dc_nc_1033 dc_nc_1034 dc_nc_1035 dc_nc_1036 dc_nc_1037 dc_nc_1038 dc_nc_1039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
