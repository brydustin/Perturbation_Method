theory OCX_nc_188
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3008: "oc_sub None 3008"
  by (oc_eval oc_nc_3008)

lemma oc_nc_3009: "oc_sub None 3009"
  by (oc_eval oc_nc_3009)

lemma oc_nc_3010: "oc_sub None 3010"
  by (oc_eval oc_nc_3010)

lemma oc_nc_3011: "oc_sub None 3011"
  by (oc_eval oc_nc_3011)

lemma oc_nc_3012: "oc_sub None 3012"
  by (oc_eval oc_nc_3012)

lemma oc_nc_3013: "oc_sub None 3013"
  by (oc_eval oc_nc_3013)

lemma oc_nc_3014: "oc_sub None 3014"
  by (oc_eval oc_nc_3014)

lemma oc_nc_3015: "oc_sub None 3015"
  by (oc_eval oc_nc_3015)

lemma oc_nc_3016: "oc_sub None 3016"
  by (oc_eval oc_nc_3016)

lemma oc_nc_3017: "oc_sub None 3017"
  by (oc_eval oc_nc_3017)

lemma oc_nc_3018: "oc_sub None 3018"
  by (oc_eval oc_nc_3018)

lemma oc_nc_3019: "oc_sub None 3019"
  by (oc_eval oc_nc_3019)

lemma oc_nc_3020: "oc_sub None 3020"
  by (oc_eval oc_nc_3020)

lemma oc_nc_3021: "oc_sub None 3021"
  by (oc_eval oc_nc_3021)

lemma oc_nc_3022: "oc_sub None 3022"
  by (oc_eval oc_nc_3022)

lemma oc_nc_3023: "oc_sub None 3023"
  by (oc_eval oc_nc_3023)

lemma upt_nc_188: "[3008..<3024] = [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]"
  by (simp add: upt_rec)

lemma sec_nc_188: "\<forall>j\<in>{16 * 188..<16 * 188 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 188..<16 * 188 + 16}"
  then have "j \<in> set [3008..<3024]" unfolding set_upt by simp
  then have "j \<in> set [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]" unfolding upt_nc_188 .
  then show "oc_sub None j" using oc_nc_3008 oc_nc_3009 oc_nc_3010 oc_nc_3011 oc_nc_3012 oc_nc_3013 oc_nc_3014 oc_nc_3015 oc_nc_3016 oc_nc_3017 oc_nc_3018 oc_nc_3019 oc_nc_3020 oc_nc_3021 oc_nc_3022 oc_nc_3023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
