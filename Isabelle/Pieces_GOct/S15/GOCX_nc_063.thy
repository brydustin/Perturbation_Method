theory GOCX_nc_063
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1008: "goc_sub None 1008"
  by (goc_eval goc_nc_1008)

lemma goc_nc_1009: "goc_sub None 1009"
  by (goc_eval goc_nc_1009)

lemma goc_nc_1010: "goc_sub None 1010"
  by (goc_eval goc_nc_1010)

lemma goc_nc_1011: "goc_sub None 1011"
  by (goc_eval goc_nc_1011)

lemma goc_nc_1012: "goc_sub None 1012"
  by (goc_eval goc_nc_1012)

lemma goc_nc_1013: "goc_sub None 1013"
  by (goc_eval goc_nc_1013)

lemma goc_nc_1014: "goc_sub None 1014"
  by (goc_eval goc_nc_1014)

lemma goc_nc_1015: "goc_sub None 1015"
  by (goc_eval goc_nc_1015)

lemma goc_nc_1016: "goc_sub None 1016"
  by (goc_eval goc_nc_1016)

lemma goc_nc_1017: "goc_sub None 1017"
  by (goc_eval goc_nc_1017)

lemma goc_nc_1018: "goc_sub None 1018"
  by (goc_eval goc_nc_1018)

lemma goc_nc_1019: "goc_sub None 1019"
  by (goc_eval goc_nc_1019)

lemma goc_nc_1020: "goc_sub None 1020"
  by (goc_eval goc_nc_1020)

lemma goc_nc_1021: "goc_sub None 1021"
  by (goc_eval goc_nc_1021)

lemma goc_nc_1022: "goc_sub None 1022"
  by (goc_eval goc_nc_1022)

lemma goc_nc_1023: "goc_sub None 1023"
  by (goc_eval goc_nc_1023)

lemma gupt_nc_063: "[1008..<1024] = [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]"
  by (simp add: upt_rec)

lemma gsec_nc_063: "\<forall>j\<in>{16 * 63..<16 * 63 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 63..<16 * 63 + 16}"
  then have "j \<in> set [1008..<1024]" unfolding set_upt by simp
  then have "j \<in> set [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]" unfolding gupt_nc_063 .
  then show "goc_sub None j" using goc_nc_1008 goc_nc_1009 goc_nc_1010 goc_nc_1011 goc_nc_1012 goc_nc_1013 goc_nc_1014 goc_nc_1015 goc_nc_1016 goc_nc_1017 goc_nc_1018 goc_nc_1019 goc_nc_1020 goc_nc_1021 goc_nc_1022 goc_nc_1023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
