theory GDCX_nc_188
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3008: "gdc_sub None 3008"
  by (gdc_eval gdc_nc_3008)

lemma gdc_nc_3009: "gdc_sub None 3009"
  by (gdc_eval gdc_nc_3009)

lemma gdc_nc_3010: "gdc_sub None 3010"
  by (gdc_eval gdc_nc_3010)

lemma gdc_nc_3011: "gdc_sub None 3011"
  by (gdc_eval gdc_nc_3011)

lemma gdc_nc_3012: "gdc_sub None 3012"
  by (gdc_eval gdc_nc_3012)

lemma gdc_nc_3013: "gdc_sub None 3013"
  by (gdc_eval gdc_nc_3013)

lemma gdc_nc_3014: "gdc_sub None 3014"
  by (gdc_eval gdc_nc_3014)

lemma gdc_nc_3015: "gdc_sub None 3015"
  by (gdc_eval gdc_nc_3015)

lemma gdc_nc_3016: "gdc_sub None 3016"
  by (gdc_eval gdc_nc_3016)

lemma gdc_nc_3017: "gdc_sub None 3017"
  by (gdc_eval gdc_nc_3017)

lemma gdc_nc_3018: "gdc_sub None 3018"
  by (gdc_eval gdc_nc_3018)

lemma gdc_nc_3019: "gdc_sub None 3019"
  by (gdc_eval gdc_nc_3019)

lemma gdc_nc_3020: "gdc_sub None 3020"
  by (gdc_eval gdc_nc_3020)

lemma gdc_nc_3021: "gdc_sub None 3021"
  by (gdc_eval gdc_nc_3021)

lemma gdc_nc_3022: "gdc_sub None 3022"
  by (gdc_eval gdc_nc_3022)

lemma gdc_nc_3023: "gdc_sub None 3023"
  by (gdc_eval gdc_nc_3023)

lemma gupt_nc_188: "[3008..<3024] = [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]"
  by (simp add: upt_rec)

lemma gsec_nc_188: "\<forall>j\<in>{16 * 188..<16 * 188 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 188..<16 * 188 + 16}"
  then have "j \<in> set [3008..<3024]" unfolding set_upt by simp
  then have "j \<in> set [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]" unfolding gupt_nc_188 .
  then show "gdc_sub None j" using gdc_nc_3008 gdc_nc_3009 gdc_nc_3010 gdc_nc_3011 gdc_nc_3012 gdc_nc_3013 gdc_nc_3014 gdc_nc_3015 gdc_nc_3016 gdc_nc_3017 gdc_nc_3018 gdc_nc_3019 gdc_nc_3020 gdc_nc_3021 gdc_nc_3022 gdc_nc_3023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
