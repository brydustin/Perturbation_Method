theory OCX_c30_188
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_3008: "oc_sub oc_b30 3008"
  by (oc_eval oc_c30_3008)

lemma oc_c30_3009: "oc_sub oc_b30 3009"
  by (oc_eval oc_c30_3009)

lemma oc_c30_3010: "oc_sub oc_b30 3010"
  by (oc_eval oc_c30_3010)

lemma oc_c30_3011: "oc_sub oc_b30 3011"
  by (oc_eval oc_c30_3011)

lemma oc_c30_3012: "oc_sub oc_b30 3012"
  by (oc_eval oc_c30_3012)

lemma oc_c30_3013: "oc_sub oc_b30 3013"
  by (oc_eval oc_c30_3013)

lemma oc_c30_3014: "oc_sub oc_b30 3014"
  by (oc_eval oc_c30_3014)

lemma oc_c30_3015: "oc_sub oc_b30 3015"
  by (oc_eval oc_c30_3015)

lemma oc_c30_3016: "oc_sub oc_b30 3016"
  by (oc_eval oc_c30_3016)

lemma oc_c30_3017: "oc_sub oc_b30 3017"
  by (oc_eval oc_c30_3017)

lemma oc_c30_3018: "oc_sub oc_b30 3018"
  by (oc_eval oc_c30_3018)

lemma oc_c30_3019: "oc_sub oc_b30 3019"
  by (oc_eval oc_c30_3019)

lemma oc_c30_3020: "oc_sub oc_b30 3020"
  by (oc_eval oc_c30_3020)

lemma oc_c30_3021: "oc_sub oc_b30 3021"
  by (oc_eval oc_c30_3021)

lemma oc_c30_3022: "oc_sub oc_b30 3022"
  by (oc_eval oc_c30_3022)

lemma oc_c30_3023: "oc_sub oc_b30 3023"
  by (oc_eval oc_c30_3023)

lemma upt_c30_188: "[3008..<3024] = [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]"
  by (simp add: upt_rec)

lemma sec_c30_188: "\<forall>j\<in>{16 * 188..<16 * 188 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 188..<16 * 188 + 16}"
  then have "j \<in> set [3008..<3024]" unfolding set_upt by simp
  then have "j \<in> set [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]" unfolding upt_c30_188 .
  then show "oc_sub oc_b30 j" using oc_c30_3008 oc_c30_3009 oc_c30_3010 oc_c30_3011 oc_c30_3012 oc_c30_3013 oc_c30_3014 oc_c30_3015 oc_c30_3016 oc_c30_3017 oc_c30_3018 oc_c30_3019 oc_c30_3020 oc_c30_3021 oc_c30_3022 oc_c30_3023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
