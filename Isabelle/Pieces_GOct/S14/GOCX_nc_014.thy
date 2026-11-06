theory GOCX_nc_014
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0224: "goc_sub None 224"
  by (goc_eval goc_nc_0224)

lemma goc_nc_0225: "goc_sub None 225"
  by (goc_eval goc_nc_0225)

lemma goc_nc_0226: "goc_sub None 226"
  by (goc_eval goc_nc_0226)

lemma goc_nc_0227: "goc_sub None 227"
  by (goc_eval goc_nc_0227)

lemma goc_nc_0228: "goc_sub None 228"
  by (goc_eval goc_nc_0228)

lemma goc_nc_0229: "goc_sub None 229"
  by (goc_eval goc_nc_0229)

lemma goc_nc_0230: "goc_sub None 230"
  by (goc_eval goc_nc_0230)

lemma goc_nc_0231: "goc_sub None 231"
  by (goc_eval goc_nc_0231)

lemma goc_nc_0232: "goc_sub None 232"
  by (goc_eval goc_nc_0232)

lemma goc_nc_0233: "goc_sub None 233"
  by (goc_eval goc_nc_0233)

lemma goc_nc_0234: "goc_sub None 234"
  by (goc_eval goc_nc_0234)

lemma goc_nc_0235: "goc_sub None 235"
  by (goc_eval goc_nc_0235)

lemma goc_nc_0236: "goc_sub None 236"
  by (goc_eval goc_nc_0236)

lemma goc_nc_0237: "goc_sub None 237"
  by (goc_eval goc_nc_0237)

lemma goc_nc_0238: "goc_sub None 238"
  by (goc_eval goc_nc_0238)

lemma goc_nc_0239: "goc_sub None 239"
  by (goc_eval goc_nc_0239)

lemma gupt_nc_014: "[224..<240] = [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]"
  by (simp add: upt_rec)

lemma gsec_nc_014: "\<forall>j\<in>{16 * 14..<16 * 14 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 14..<16 * 14 + 16}"
  then have "j \<in> set [224..<240]" unfolding set_upt by simp
  then have "j \<in> set [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]" unfolding gupt_nc_014 .
  then show "goc_sub None j" using goc_nc_0224 goc_nc_0225 goc_nc_0226 goc_nc_0227 goc_nc_0228 goc_nc_0229 goc_nc_0230 goc_nc_0231 goc_nc_0232 goc_nc_0233 goc_nc_0234 goc_nc_0235 goc_nc_0236 goc_nc_0237 goc_nc_0238 goc_nc_0239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
