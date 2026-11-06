theory GDCX_nc_014
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0224: "gdc_sub None 224"
  by (gdc_eval gdc_nc_0224)

lemma gdc_nc_0225: "gdc_sub None 225"
  by (gdc_eval gdc_nc_0225)

lemma gdc_nc_0226: "gdc_sub None 226"
  by (gdc_eval gdc_nc_0226)

lemma gdc_nc_0227: "gdc_sub None 227"
  by (gdc_eval gdc_nc_0227)

lemma gdc_nc_0228: "gdc_sub None 228"
  by (gdc_eval gdc_nc_0228)

lemma gdc_nc_0229: "gdc_sub None 229"
  by (gdc_eval gdc_nc_0229)

lemma gdc_nc_0230: "gdc_sub None 230"
  by (gdc_eval gdc_nc_0230)

lemma gdc_nc_0231: "gdc_sub None 231"
  by (gdc_eval gdc_nc_0231)

lemma gdc_nc_0232: "gdc_sub None 232"
  by (gdc_eval gdc_nc_0232)

lemma gdc_nc_0233: "gdc_sub None 233"
  by (gdc_eval gdc_nc_0233)

lemma gdc_nc_0234: "gdc_sub None 234"
  by (gdc_eval gdc_nc_0234)

lemma gdc_nc_0235: "gdc_sub None 235"
  by (gdc_eval gdc_nc_0235)

lemma gdc_nc_0236: "gdc_sub None 236"
  by (gdc_eval gdc_nc_0236)

lemma gdc_nc_0237: "gdc_sub None 237"
  by (gdc_eval gdc_nc_0237)

lemma gdc_nc_0238: "gdc_sub None 238"
  by (gdc_eval gdc_nc_0238)

lemma gdc_nc_0239: "gdc_sub None 239"
  by (gdc_eval gdc_nc_0239)

lemma gupt_nc_014: "[224..<240] = [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]"
  by (simp add: upt_rec)

lemma gsec_nc_014: "\<forall>j\<in>{16 * 14..<16 * 14 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 14..<16 * 14 + 16}"
  then have "j \<in> set [224..<240]" unfolding set_upt by simp
  then have "j \<in> set [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]" unfolding gupt_nc_014 .
  then show "gdc_sub None j" using gdc_nc_0224 gdc_nc_0225 gdc_nc_0226 gdc_nc_0227 gdc_nc_0228 gdc_nc_0229 gdc_nc_0230 gdc_nc_0231 gdc_nc_0232 gdc_nc_0233 gdc_nc_0234 gdc_nc_0235 gdc_nc_0236 gdc_nc_0237 gdc_nc_0238 gdc_nc_0239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
