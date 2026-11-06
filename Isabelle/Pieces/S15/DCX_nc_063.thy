theory DCX_nc_063
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1008: "dc_sub None 1008"
  by (dc_eval dc_nc_1008)

lemma dc_nc_1009: "dc_sub None 1009"
  by (dc_eval dc_nc_1009)

lemma dc_nc_1010: "dc_sub None 1010"
  by (dc_eval dc_nc_1010)

lemma dc_nc_1011: "dc_sub None 1011"
  by (dc_eval dc_nc_1011)

lemma dc_nc_1012: "dc_sub None 1012"
  by (dc_eval dc_nc_1012)

lemma dc_nc_1013: "dc_sub None 1013"
  by (dc_eval dc_nc_1013)

lemma dc_nc_1014: "dc_sub None 1014"
  by (dc_eval dc_nc_1014)

lemma dc_nc_1015: "dc_sub None 1015"
  by (dc_eval dc_nc_1015)

lemma dc_nc_1016: "dc_sub None 1016"
  by (dc_eval dc_nc_1016)

lemma dc_nc_1017: "dc_sub None 1017"
  by (dc_eval dc_nc_1017)

lemma dc_nc_1018: "dc_sub None 1018"
  by (dc_eval dc_nc_1018)

lemma dc_nc_1019: "dc_sub None 1019"
  by (dc_eval dc_nc_1019)

lemma dc_nc_1020: "dc_sub None 1020"
  by (dc_eval dc_nc_1020)

lemma dc_nc_1021: "dc_sub None 1021"
  by (dc_eval dc_nc_1021)

lemma dc_nc_1022: "dc_sub None 1022"
  by (dc_eval dc_nc_1022)

lemma dc_nc_1023: "dc_sub None 1023"
  by (dc_eval dc_nc_1023)

lemma upt_nc_063: "[1008..<1024] = [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]"
  by (simp add: upt_rec)

lemma sec_nc_063: "\<forall>j\<in>{16 * 63..<16 * 63 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 63..<16 * 63 + 16}"
  then have "j \<in> set [1008..<1024]" unfolding set_upt by simp
  then have "j \<in> set [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]" unfolding upt_nc_063 .
  then show "dc_sub None j" using dc_nc_1008 dc_nc_1009 dc_nc_1010 dc_nc_1011 dc_nc_1012 dc_nc_1013 dc_nc_1014 dc_nc_1015 dc_nc_1016 dc_nc_1017 dc_nc_1018 dc_nc_1019 dc_nc_1020 dc_nc_1021 dc_nc_1022 dc_nc_1023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
