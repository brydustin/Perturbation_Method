theory DCX_nc_014
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0224: "dc_sub None 224"
  by (dc_eval dc_nc_0224)

lemma dc_nc_0225: "dc_sub None 225"
  by (dc_eval dc_nc_0225)

lemma dc_nc_0226: "dc_sub None 226"
  by (dc_eval dc_nc_0226)

lemma dc_nc_0227: "dc_sub None 227"
  by (dc_eval dc_nc_0227)

lemma dc_nc_0228: "dc_sub None 228"
  by (dc_eval dc_nc_0228)

lemma dc_nc_0229: "dc_sub None 229"
  by (dc_eval dc_nc_0229)

lemma dc_nc_0230: "dc_sub None 230"
  by (dc_eval dc_nc_0230)

lemma dc_nc_0231: "dc_sub None 231"
  by (dc_eval dc_nc_0231)

lemma dc_nc_0232: "dc_sub None 232"
  by (dc_eval dc_nc_0232)

lemma dc_nc_0233: "dc_sub None 233"
  by (dc_eval dc_nc_0233)

lemma dc_nc_0234: "dc_sub None 234"
  by (dc_eval dc_nc_0234)

lemma dc_nc_0235: "dc_sub None 235"
  by (dc_eval dc_nc_0235)

lemma dc_nc_0236: "dc_sub None 236"
  by (dc_eval dc_nc_0236)

lemma dc_nc_0237: "dc_sub None 237"
  by (dc_eval dc_nc_0237)

lemma dc_nc_0238: "dc_sub None 238"
  by (dc_eval dc_nc_0238)

lemma dc_nc_0239: "dc_sub None 239"
  by (dc_eval dc_nc_0239)

lemma upt_nc_014: "[224..<240] = [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]"
  by (simp add: upt_rec)

lemma sec_nc_014: "\<forall>j\<in>{16 * 14..<16 * 14 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 14..<16 * 14 + 16}"
  then have "j \<in> set [224..<240]" unfolding set_upt by simp
  then have "j \<in> set [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]" unfolding upt_nc_014 .
  then show "dc_sub None j" using dc_nc_0224 dc_nc_0225 dc_nc_0226 dc_nc_0227 dc_nc_0228 dc_nc_0229 dc_nc_0230 dc_nc_0231 dc_nc_0232 dc_nc_0233 dc_nc_0234 dc_nc_0235 dc_nc_0236 dc_nc_0237 dc_nc_0238 dc_nc_0239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
