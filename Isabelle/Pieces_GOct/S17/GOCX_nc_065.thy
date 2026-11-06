theory GOCX_nc_065
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1040: "goc_sub None 1040"
  by (goc_eval goc_nc_1040)

lemma goc_nc_1041: "goc_sub None 1041"
  by (goc_eval goc_nc_1041)

lemma goc_nc_1042: "goc_sub None 1042"
  by (goc_eval goc_nc_1042)

lemma goc_nc_1043: "goc_sub None 1043"
  by (goc_eval goc_nc_1043)

lemma goc_nc_1044: "goc_sub None 1044"
  by (goc_eval goc_nc_1044)

lemma goc_nc_1045: "goc_sub None 1045"
  by (goc_eval goc_nc_1045)

lemma goc_nc_1046: "goc_sub None 1046"
  by (goc_eval goc_nc_1046)

lemma goc_nc_1047: "goc_sub None 1047"
  by (goc_eval goc_nc_1047)

lemma goc_nc_1048: "goc_sub None 1048"
  by (goc_eval goc_nc_1048)

lemma goc_nc_1049: "goc_sub None 1049"
  by (goc_eval goc_nc_1049)

lemma goc_nc_1050: "goc_sub None 1050"
  by (goc_eval goc_nc_1050)

lemma goc_nc_1051: "goc_sub None 1051"
  by (goc_eval goc_nc_1051)

lemma goc_nc_1052: "goc_sub None 1052"
  by (goc_eval goc_nc_1052)

lemma goc_nc_1053: "goc_sub None 1053"
  by (goc_eval goc_nc_1053)

lemma goc_nc_1054: "goc_sub None 1054"
  by (goc_eval goc_nc_1054)

lemma goc_nc_1055: "goc_sub None 1055"
  by (goc_eval goc_nc_1055)

lemma gupt_nc_065: "[1040..<1056] = [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]"
  by (simp add: upt_rec)

lemma gsec_nc_065: "\<forall>j\<in>{16 * 65..<16 * 65 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 65..<16 * 65 + 16}"
  then have "j \<in> set [1040..<1056]" unfolding set_upt by simp
  then have "j \<in> set [1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055]" unfolding gupt_nc_065 .
  then show "goc_sub None j" using goc_nc_1040 goc_nc_1041 goc_nc_1042 goc_nc_1043 goc_nc_1044 goc_nc_1045 goc_nc_1046 goc_nc_1047 goc_nc_1048 goc_nc_1049 goc_nc_1050 goc_nc_1051 goc_nc_1052 goc_nc_1053 goc_nc_1054 goc_nc_1055
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
