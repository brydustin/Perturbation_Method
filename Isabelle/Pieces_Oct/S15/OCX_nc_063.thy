theory OCX_nc_063
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1008: "oc_sub None 1008"
  by (oc_eval oc_nc_1008)

lemma oc_nc_1009: "oc_sub None 1009"
  by (oc_eval oc_nc_1009)

lemma oc_nc_1010: "oc_sub None 1010"
  by (oc_eval oc_nc_1010)

lemma oc_nc_1011: "oc_sub None 1011"
  by (oc_eval oc_nc_1011)

lemma oc_nc_1012: "oc_sub None 1012"
  by (oc_eval oc_nc_1012)

lemma oc_nc_1013: "oc_sub None 1013"
  by (oc_eval oc_nc_1013)

lemma oc_nc_1014: "oc_sub None 1014"
  by (oc_eval oc_nc_1014)

lemma oc_nc_1015: "oc_sub None 1015"
  by (oc_eval oc_nc_1015)

lemma oc_nc_1016: "oc_sub None 1016"
  by (oc_eval oc_nc_1016)

lemma oc_nc_1017: "oc_sub None 1017"
  by (oc_eval oc_nc_1017)

lemma oc_nc_1018: "oc_sub None 1018"
  by (oc_eval oc_nc_1018)

lemma oc_nc_1019: "oc_sub None 1019"
  by (oc_eval oc_nc_1019)

lemma oc_nc_1020: "oc_sub None 1020"
  by (oc_eval oc_nc_1020)

lemma oc_nc_1021: "oc_sub None 1021"
  by (oc_eval oc_nc_1021)

lemma oc_nc_1022: "oc_sub None 1022"
  by (oc_eval oc_nc_1022)

lemma oc_nc_1023: "oc_sub None 1023"
  by (oc_eval oc_nc_1023)

lemma upt_nc_063: "[1008..<1024] = [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]"
  by (simp add: upt_rec)

lemma sec_nc_063: "\<forall>j\<in>{16 * 63..<16 * 63 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 63..<16 * 63 + 16}"
  then have "j \<in> set [1008..<1024]" unfolding set_upt by simp
  then have "j \<in> set [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]" unfolding upt_nc_063 .
  then show "oc_sub None j" using oc_nc_1008 oc_nc_1009 oc_nc_1010 oc_nc_1011 oc_nc_1012 oc_nc_1013 oc_nc_1014 oc_nc_1015 oc_nc_1016 oc_nc_1017 oc_nc_1018 oc_nc_1019 oc_nc_1020 oc_nc_1021 oc_nc_1022 oc_nc_1023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
