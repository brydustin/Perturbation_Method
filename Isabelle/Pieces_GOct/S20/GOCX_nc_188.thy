theory GOCX_nc_188
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3008: "goc_sub None 3008"
  by (goc_eval goc_nc_3008)

lemma goc_nc_3009: "goc_sub None 3009"
  by (goc_eval goc_nc_3009)

lemma goc_nc_3010: "goc_sub None 3010"
  by (goc_eval goc_nc_3010)

lemma goc_nc_3011: "goc_sub None 3011"
  by (goc_eval goc_nc_3011)

lemma goc_nc_3012: "goc_sub None 3012"
  by (goc_eval goc_nc_3012)

lemma goc_nc_3013: "goc_sub None 3013"
  by (goc_eval goc_nc_3013)

lemma goc_nc_3014: "goc_sub None 3014"
  by (goc_eval goc_nc_3014)

lemma goc_nc_3015: "goc_sub None 3015"
  by (goc_eval goc_nc_3015)

lemma goc_nc_3016: "goc_sub None 3016"
  by (goc_eval goc_nc_3016)

lemma goc_nc_3017: "goc_sub None 3017"
  by (goc_eval goc_nc_3017)

lemma goc_nc_3018: "goc_sub None 3018"
  by (goc_eval goc_nc_3018)

lemma goc_nc_3019: "goc_sub None 3019"
  by (goc_eval goc_nc_3019)

lemma goc_nc_3020: "goc_sub None 3020"
  by (goc_eval goc_nc_3020)

lemma goc_nc_3021: "goc_sub None 3021"
  by (goc_eval goc_nc_3021)

lemma goc_nc_3022: "goc_sub None 3022"
  by (goc_eval goc_nc_3022)

lemma goc_nc_3023: "goc_sub None 3023"
  by (goc_eval goc_nc_3023)

lemma gupt_nc_188: "[3008..<3024] = [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]"
  by (simp add: upt_rec)

lemma gsec_nc_188: "\<forall>j\<in>{16 * 188..<16 * 188 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 188..<16 * 188 + 16}"
  then have "j \<in> set [3008..<3024]" unfolding set_upt by simp
  then have "j \<in> set [3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3020, 3021, 3022, 3023]" unfolding gupt_nc_188 .
  then show "goc_sub None j" using goc_nc_3008 goc_nc_3009 goc_nc_3010 goc_nc_3011 goc_nc_3012 goc_nc_3013 goc_nc_3014 goc_nc_3015 goc_nc_3016 goc_nc_3017 goc_nc_3018 goc_nc_3019 goc_nc_3020 goc_nc_3021 goc_nc_3022 goc_nc_3023
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
