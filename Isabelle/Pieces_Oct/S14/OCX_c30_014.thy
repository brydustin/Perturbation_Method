theory OCX_c30_014
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0224: "oc_sub oc_b30 224"
  by (oc_eval oc_c30_0224)

lemma oc_c30_0225: "oc_sub oc_b30 225"
  by (oc_eval oc_c30_0225)

lemma oc_c30_0226: "oc_sub oc_b30 226"
  by (oc_eval oc_c30_0226)

lemma oc_c30_0227: "oc_sub oc_b30 227"
  by (oc_eval oc_c30_0227)

lemma oc_c30_0228: "oc_sub oc_b30 228"
  by (oc_eval oc_c30_0228)

lemma oc_c30_0229: "oc_sub oc_b30 229"
  by (oc_eval oc_c30_0229)

lemma oc_c30_0230: "oc_sub oc_b30 230"
  by (oc_eval oc_c30_0230)

lemma oc_c30_0231: "oc_sub oc_b30 231"
  by (oc_eval oc_c30_0231)

lemma oc_c30_0232: "oc_sub oc_b30 232"
  by (oc_eval oc_c30_0232)

lemma oc_c30_0233: "oc_sub oc_b30 233"
  by (oc_eval oc_c30_0233)

lemma oc_c30_0234: "oc_sub oc_b30 234"
  by (oc_eval oc_c30_0234)

lemma oc_c30_0235: "oc_sub oc_b30 235"
  by (oc_eval oc_c30_0235)

lemma oc_c30_0236: "oc_sub oc_b30 236"
  by (oc_eval oc_c30_0236)

lemma oc_c30_0237: "oc_sub oc_b30 237"
  by (oc_eval oc_c30_0237)

lemma oc_c30_0238: "oc_sub oc_b30 238"
  by (oc_eval oc_c30_0238)

lemma oc_c30_0239: "oc_sub oc_b30 239"
  by (oc_eval oc_c30_0239)

lemma upt_c30_014: "[224..<240] = [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]"
  by (simp add: upt_rec)

lemma sec_c30_014: "\<forall>j\<in>{16 * 14..<16 * 14 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 14..<16 * 14 + 16}"
  then have "j \<in> set [224..<240]" unfolding set_upt by simp
  then have "j \<in> set [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]" unfolding upt_c30_014 .
  then show "oc_sub oc_b30 j" using oc_c30_0224 oc_c30_0225 oc_c30_0226 oc_c30_0227 oc_c30_0228 oc_c30_0229 oc_c30_0230 oc_c30_0231 oc_c30_0232 oc_c30_0233 oc_c30_0234 oc_c30_0235 oc_c30_0236 oc_c30_0237 oc_c30_0238 oc_c30_0239
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
