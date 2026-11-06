theory GDCX_nc_063
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1008: "gdc_sub None 1008"
  by (gdc_eval gdc_nc_1008)

lemma gdc_nc_1009: "gdc_sub None 1009"
  by (gdc_eval gdc_nc_1009)

lemma gdc_nc_1010: "gdc_sub None 1010"
  by (gdc_eval gdc_nc_1010)

lemma gdc_nc_1011: "gdc_sub None 1011"
  by (gdc_eval gdc_nc_1011)

lemma gdc_nc_1012: "gdc_sub None 1012"
  by (gdc_eval gdc_nc_1012)

lemma gdc_nc_1013: "gdc_sub None 1013"
  by (gdc_eval gdc_nc_1013)

lemma gdc_nc_1014: "gdc_sub None 1014"
  by (gdc_eval gdc_nc_1014)

lemma gdc_nc_1015: "gdc_sub None 1015"
  by (gdc_eval gdc_nc_1015)

lemma gdc_nc_1016: "gdc_sub None 1016"
  by (gdc_eval gdc_nc_1016)

lemma gdc_nc_1017: "gdc_sub None 1017"
  by (gdc_eval gdc_nc_1017)

lemma gdc_nc_1018: "gdc_sub None 1018"
  by (gdc_eval gdc_nc_1018)

lemma gdc_nc_1019: "gdc_sub None 1019"
  by (gdc_eval gdc_nc_1019)

lemma gdc_nc_1020: "gdc_sub None 1020"
  by (gdc_eval gdc_nc_1020)

lemma gdc_nc_1021: "gdc_sub None 1021"
  by (gdc_eval gdc_nc_1021)

lemma gdc_nc_1022: "gdc_sub None 1022"
  by (gdc_eval gdc_nc_1022)

lemma gdc_nc_1023: "gdc_sub None 1023"
  by (gdc_eval gdc_nc_1023)

lemma gupt_nc_063: "[1008..<1024] = [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]"
  by (simp add: upt_rec)

lemma gsec_nc_063: "\<forall>j\<in>{16 * 63..<16 * 63 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 63..<16 * 63 + 16}"
  then have "j \<in> set [1008..<1024]" unfolding set_upt by simp
  then have "j \<in> set [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]" unfolding gupt_nc_063 .
  then show "gdc_sub None j" using gdc_nc_1008 gdc_nc_1009 gdc_nc_1010 gdc_nc_1011 gdc_nc_1012 gdc_nc_1013 gdc_nc_1014 gdc_nc_1015 gdc_nc_1016 gdc_nc_1017 gdc_nc_1018 gdc_nc_1019 gdc_nc_1020 gdc_nc_1021 gdc_nc_1022 gdc_nc_1023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
