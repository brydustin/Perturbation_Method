theory GDCX_nc_064
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1024: "gdc_sub None 1024"
  by (gdc_eval gdc_nc_1024)

lemma gdc_nc_1025: "gdc_sub None 1025"
  by (gdc_eval gdc_nc_1025)

lemma gdc_nc_1026: "gdc_sub None 1026"
  by (gdc_eval gdc_nc_1026)

lemma gdc_nc_1027: "gdc_sub None 1027"
  by (gdc_eval gdc_nc_1027)

lemma gdc_nc_1028: "gdc_sub None 1028"
  by (gdc_eval gdc_nc_1028)

lemma gdc_nc_1029: "gdc_sub None 1029"
  by (gdc_eval gdc_nc_1029)

lemma gdc_nc_1030: "gdc_sub None 1030"
  by (gdc_eval gdc_nc_1030)

lemma gdc_nc_1031: "gdc_sub None 1031"
  by (gdc_eval gdc_nc_1031)

lemma gdc_nc_1032: "gdc_sub None 1032"
  by (gdc_eval gdc_nc_1032)

lemma gdc_nc_1033: "gdc_sub None 1033"
  by (gdc_eval gdc_nc_1033)

lemma gdc_nc_1034: "gdc_sub None 1034"
  by (gdc_eval gdc_nc_1034)

lemma gdc_nc_1035: "gdc_sub None 1035"
  by (gdc_eval gdc_nc_1035)

lemma gdc_nc_1036: "gdc_sub None 1036"
  by (gdc_eval gdc_nc_1036)

lemma gdc_nc_1037: "gdc_sub None 1037"
  by (gdc_eval gdc_nc_1037)

lemma gdc_nc_1038: "gdc_sub None 1038"
  by (gdc_eval gdc_nc_1038)

lemma gdc_nc_1039: "gdc_sub None 1039"
  by (gdc_eval gdc_nc_1039)

lemma gupt_nc_064: "[1024..<1040] = [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]"
  by (simp add: upt_rec)

lemma gsec_nc_064: "\<forall>j\<in>{16 * 64..<16 * 64 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 64..<16 * 64 + 16}"
  then have "j \<in> set [1024..<1040]" unfolding set_upt by simp
  then have "j \<in> set [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]" unfolding gupt_nc_064 .
  then show "gdc_sub None j" using gdc_nc_1024 gdc_nc_1025 gdc_nc_1026 gdc_nc_1027 gdc_nc_1028 gdc_nc_1029 gdc_nc_1030 gdc_nc_1031 gdc_nc_1032 gdc_nc_1033 gdc_nc_1034 gdc_nc_1035 gdc_nc_1036 gdc_nc_1037 gdc_nc_1038 gdc_nc_1039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
