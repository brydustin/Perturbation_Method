theory OCX_nc_014
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0224: "oc_sub None 224"
  by (oc_eval oc_nc_0224)

lemma oc_nc_0225: "oc_sub None 225"
  by (oc_eval oc_nc_0225)

lemma oc_nc_0226: "oc_sub None 226"
  by (oc_eval oc_nc_0226)

lemma oc_nc_0227: "oc_sub None 227"
  by (oc_eval oc_nc_0227)

lemma oc_nc_0228: "oc_sub None 228"
  by (oc_eval oc_nc_0228)

lemma oc_nc_0229: "oc_sub None 229"
  by (oc_eval oc_nc_0229)

lemma oc_nc_0230: "oc_sub None 230"
  by (oc_eval oc_nc_0230)

lemma oc_nc_0231: "oc_sub None 231"
  by (oc_eval oc_nc_0231)

lemma oc_nc_0232: "oc_sub None 232"
  by (oc_eval oc_nc_0232)

lemma oc_nc_0233: "oc_sub None 233"
  by (oc_eval oc_nc_0233)

lemma oc_nc_0234: "oc_sub None 234"
  by (oc_eval oc_nc_0234)

lemma oc_nc_0235: "oc_sub None 235"
  by (oc_eval oc_nc_0235)

lemma oc_nc_0236: "oc_sub None 236"
  by (oc_eval oc_nc_0236)

lemma oc_nc_0237: "oc_sub None 237"
  by (oc_eval oc_nc_0237)

lemma oc_nc_0238: "oc_sub None 238"
  by (oc_eval oc_nc_0238)

lemma oc_nc_0239: "oc_sub None 239"
  by (oc_eval oc_nc_0239)

lemma upt_nc_014: "[224..<240] = [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]"
  by (simp add: upt_rec)

lemma sec_nc_014: "\<forall>j\<in>{16 * 14..<16 * 14 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 14..<16 * 14 + 16}"
  then have "j \<in> set [224..<240]" unfolding set_upt by simp
  then have "j \<in> set [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]" unfolding upt_nc_014 .
  then show "oc_sub None j" using oc_nc_0224 oc_nc_0225 oc_nc_0226 oc_nc_0227 oc_nc_0228 oc_nc_0229 oc_nc_0230 oc_nc_0231 oc_nc_0232 oc_nc_0233 oc_nc_0234 oc_nc_0235 oc_nc_0236 oc_nc_0237 oc_nc_0238 oc_nc_0239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
