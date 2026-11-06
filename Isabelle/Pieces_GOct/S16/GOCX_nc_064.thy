theory GOCX_nc_064
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1024: "goc_sub None 1024"
  by (goc_eval goc_nc_1024)

lemma goc_nc_1025: "goc_sub None 1025"
  by (goc_eval goc_nc_1025)

lemma goc_nc_1026: "goc_sub None 1026"
  by (goc_eval goc_nc_1026)

lemma goc_nc_1027: "goc_sub None 1027"
  by (goc_eval goc_nc_1027)

lemma goc_nc_1028: "goc_sub None 1028"
  by (goc_eval goc_nc_1028)

lemma goc_nc_1029: "goc_sub None 1029"
  by (goc_eval goc_nc_1029)

lemma goc_nc_1030: "goc_sub None 1030"
  by (goc_eval goc_nc_1030)

lemma goc_nc_1031: "goc_sub None 1031"
  by (goc_eval goc_nc_1031)

lemma goc_nc_1032: "goc_sub None 1032"
  by (goc_eval goc_nc_1032)

lemma goc_nc_1033: "goc_sub None 1033"
  by (goc_eval goc_nc_1033)

lemma goc_nc_1034: "goc_sub None 1034"
  by (goc_eval goc_nc_1034)

lemma goc_nc_1035: "goc_sub None 1035"
  by (goc_eval goc_nc_1035)

lemma goc_nc_1036: "goc_sub None 1036"
  by (goc_eval goc_nc_1036)

lemma goc_nc_1037: "goc_sub None 1037"
  by (goc_eval goc_nc_1037)

lemma goc_nc_1038: "goc_sub None 1038"
  by (goc_eval goc_nc_1038)

lemma goc_nc_1039: "goc_sub None 1039"
  by (goc_eval goc_nc_1039)

lemma gupt_nc_064: "[1024..<1040] = [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]"
  by (simp add: upt_rec)

lemma gsec_nc_064: "\<forall>j\<in>{16 * 64..<16 * 64 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 64..<16 * 64 + 16}"
  then have "j \<in> set [1024..<1040]" unfolding set_upt by simp
  then have "j \<in> set [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039]" unfolding gupt_nc_064 .
  then show "goc_sub None j" using goc_nc_1024 goc_nc_1025 goc_nc_1026 goc_nc_1027 goc_nc_1028 goc_nc_1029 goc_nc_1030 goc_nc_1031 goc_nc_1032 goc_nc_1033 goc_nc_1034 goc_nc_1035 goc_nc_1036 goc_nc_1037 goc_nc_1038 goc_nc_1039
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
