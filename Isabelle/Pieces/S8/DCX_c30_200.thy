theory DCX_c30_200
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_3200: "dc_sub dc_b30 3200"
  by (dc_eval dc_c30_3200)

lemma dc_c30_3201: "dc_sub dc_b30 3201"
  by (dc_eval dc_c30_3201)

lemma dc_c30_3202: "dc_sub dc_b30 3202"
  by (dc_eval dc_c30_3202)

lemma dc_c30_3203: "dc_sub dc_b30 3203"
  by (dc_eval dc_c30_3203)

lemma dc_c30_3204: "dc_sub dc_b30 3204"
  by (dc_eval dc_c30_3204)

lemma dc_c30_3205: "dc_sub dc_b30 3205"
  by (dc_eval dc_c30_3205)

lemma dc_c30_3206: "dc_sub dc_b30 3206"
  by (dc_eval dc_c30_3206)

lemma dc_c30_3207: "dc_sub dc_b30 3207"
  by (dc_eval dc_c30_3207)

lemma dc_c30_3208: "dc_sub dc_b30 3208"
  by (dc_eval dc_c30_3208)

lemma dc_c30_3209: "dc_sub dc_b30 3209"
  by (dc_eval dc_c30_3209)

lemma dc_c30_3210: "dc_sub dc_b30 3210"
  by (dc_eval dc_c30_3210)

lemma dc_c30_3211: "dc_sub dc_b30 3211"
  by (dc_eval dc_c30_3211)

lemma dc_c30_3212: "dc_sub dc_b30 3212"
  by (dc_eval dc_c30_3212)

lemma dc_c30_3213: "dc_sub dc_b30 3213"
  by (dc_eval dc_c30_3213)

lemma dc_c30_3214: "dc_sub dc_b30 3214"
  by (dc_eval dc_c30_3214)

lemma dc_c30_3215: "dc_sub dc_b30 3215"
  by (dc_eval dc_c30_3215)

lemma upt_c30_200: "[3200..<3216] = [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]"
  by (simp add: upt_rec)

lemma sec_c30_200: "\<forall>j\<in>{16 * 200..<16 * 200 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 200..<16 * 200 + 16}"
  then have "j \<in> set [3200..<3216]" unfolding set_upt by simp
  then have "j \<in> set [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]" unfolding upt_c30_200 .
  then show "dc_sub dc_b30 j" using dc_c30_3200 dc_c30_3201 dc_c30_3202 dc_c30_3203 dc_c30_3204 dc_c30_3205 dc_c30_3206 dc_c30_3207 dc_c30_3208 dc_c30_3209 dc_c30_3210 dc_c30_3211 dc_c30_3212 dc_c30_3213 dc_c30_3214 dc_c30_3215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
