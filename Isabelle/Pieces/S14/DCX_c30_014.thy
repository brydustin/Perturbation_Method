theory DCX_c30_014
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0224: "dc_sub dc_b30 224"
  by (dc_eval dc_c30_0224)

lemma dc_c30_0225: "dc_sub dc_b30 225"
  by (dc_eval dc_c30_0225)

lemma dc_c30_0226: "dc_sub dc_b30 226"
  by (dc_eval dc_c30_0226)

lemma dc_c30_0227: "dc_sub dc_b30 227"
  by (dc_eval dc_c30_0227)

lemma dc_c30_0228: "dc_sub dc_b30 228"
  by (dc_eval dc_c30_0228)

lemma dc_c30_0229: "dc_sub dc_b30 229"
  by (dc_eval dc_c30_0229)

lemma dc_c30_0230: "dc_sub dc_b30 230"
  by (dc_eval dc_c30_0230)

lemma dc_c30_0231: "dc_sub dc_b30 231"
  by (dc_eval dc_c30_0231)

lemma dc_c30_0232: "dc_sub dc_b30 232"
  by (dc_eval dc_c30_0232)

lemma dc_c30_0233: "dc_sub dc_b30 233"
  by (dc_eval dc_c30_0233)

lemma dc_c30_0234: "dc_sub dc_b30 234"
  by (dc_eval dc_c30_0234)

lemma dc_c30_0235: "dc_sub dc_b30 235"
  by (dc_eval dc_c30_0235)

lemma dc_c30_0236: "dc_sub dc_b30 236"
  by (dc_eval dc_c30_0236)

lemma dc_c30_0237: "dc_sub dc_b30 237"
  by (dc_eval dc_c30_0237)

lemma dc_c30_0238: "dc_sub dc_b30 238"
  by (dc_eval dc_c30_0238)

lemma dc_c30_0239: "dc_sub dc_b30 239"
  by (dc_eval dc_c30_0239)

lemma upt_c30_014: "[224..<240] = [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]"
  by (simp add: upt_rec)

lemma sec_c30_014: "\<forall>j\<in>{16 * 14..<16 * 14 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 14..<16 * 14 + 16}"
  then have "j \<in> set [224..<240]" unfolding set_upt by simp
  then have "j \<in> set [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]" unfolding upt_c30_014 .
  then show "dc_sub dc_b30 j" using dc_c30_0224 dc_c30_0225 dc_c30_0226 dc_c30_0227 dc_c30_0228 dc_c30_0229 dc_c30_0230 dc_c30_0231 dc_c30_0232 dc_c30_0233 dc_c30_0234 dc_c30_0235 dc_c30_0236 dc_c30_0237 dc_c30_0238 dc_c30_0239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
