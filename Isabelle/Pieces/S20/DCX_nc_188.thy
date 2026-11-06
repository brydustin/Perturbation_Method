theory DCX_nc_188
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3008: "dc_sub None 3008"
  by (dc_eval dc_nc_3008)

lemma dc_nc_3009: "dc_sub None 3009"
  by (dc_eval dc_nc_3009)

lemma dc_nc_3010: "dc_sub None 3010"
  by (dc_eval dc_nc_3010)

lemma dc_nc_3011: "dc_sub None 3011"
  by (dc_eval dc_nc_3011)

lemma dc_nc_3012: "dc_sub None 3012"
  by (dc_eval dc_nc_3012)

lemma dc_nc_3013: "dc_sub None 3013"
  by (dc_eval dc_nc_3013)

lemma dc_nc_3014: "dc_sub None 3014"
  by (dc_eval dc_nc_3014)

lemma dc_nc_3015: "dc_sub None 3015"
  by (dc_eval dc_nc_3015)

lemma dc_nc_3016: "dc_sub None 3016"
  by (dc_eval dc_nc_3016)

lemma dc_nc_3017: "dc_sub None 3017"
  by (dc_eval dc_nc_3017)

lemma dc_nc_3018: "dc_sub None 3018"
  by (dc_eval dc_nc_3018)

lemma dc_nc_3019: "dc_sub None 3019"
  by (dc_eval dc_nc_3019)

lemma dc_nc_3020: "dc_sub None 3020"
  by (dc_eval dc_nc_3020)

lemma dc_nc_3021: "dc_sub None 3021"
  by (dc_eval dc_nc_3021)

lemma dc_nc_3022: "dc_sub None 3022"
  by (dc_eval dc_nc_3022)

lemma dc_nc_3023: "dc_sub None 3023"
  by (dc_eval dc_nc_3023)

lemma upt_nc_188: "[3008..<3024] = [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]"
  by (simp add: upt_rec)

lemma sec_nc_188: "\<forall>j\<in>{16 * 188..<16 * 188 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 188..<16 * 188 + 16}"
  then have "j \<in> set [3008..<3024]" unfolding set_upt by simp
  then have "j \<in> set [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]" unfolding upt_nc_188 .
  then show "dc_sub None j" using dc_nc_3008 dc_nc_3009 dc_nc_3010 dc_nc_3011 dc_nc_3012 dc_nc_3013 dc_nc_3014 dc_nc_3015 dc_nc_3016 dc_nc_3017 dc_nc_3018 dc_nc_3019 dc_nc_3020 dc_nc_3021 dc_nc_3022 dc_nc_3023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
