theory DCX_nc_200
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_3200: "dc_sub None 3200"
  by (dc_eval dc_nc_3200)

lemma dc_nc_3201: "dc_sub None 3201"
  by (dc_eval dc_nc_3201)

lemma dc_nc_3202: "dc_sub None 3202"
  by (dc_eval dc_nc_3202)

lemma dc_nc_3203: "dc_sub None 3203"
  by (dc_eval dc_nc_3203)

lemma dc_nc_3204: "dc_sub None 3204"
  by (dc_eval dc_nc_3204)

lemma dc_nc_3205: "dc_sub None 3205"
  by (dc_eval dc_nc_3205)

lemma dc_nc_3206: "dc_sub None 3206"
  by (dc_eval dc_nc_3206)

lemma dc_nc_3207: "dc_sub None 3207"
  by (dc_eval dc_nc_3207)

lemma dc_nc_3208: "dc_sub None 3208"
  by (dc_eval dc_nc_3208)

lemma dc_nc_3209: "dc_sub None 3209"
  by (dc_eval dc_nc_3209)

lemma dc_nc_3210: "dc_sub None 3210"
  by (dc_eval dc_nc_3210)

lemma dc_nc_3211: "dc_sub None 3211"
  by (dc_eval dc_nc_3211)

lemma dc_nc_3212: "dc_sub None 3212"
  by (dc_eval dc_nc_3212)

lemma dc_nc_3213: "dc_sub None 3213"
  by (dc_eval dc_nc_3213)

lemma dc_nc_3214: "dc_sub None 3214"
  by (dc_eval dc_nc_3214)

lemma dc_nc_3215: "dc_sub None 3215"
  by (dc_eval dc_nc_3215)

lemma upt_nc_200: "[3200..<3216] = [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]"
  by (simp add: upt_rec)

lemma sec_nc_200: "\<forall>j\<in>{16 * 200..<16 * 200 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 200..<16 * 200 + 16}"
  then have "j \<in> set [3200..<3216]" unfolding set_upt by simp
  then have "j \<in> set [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]" unfolding upt_nc_200 .
  then show "dc_sub None j" using dc_nc_3200 dc_nc_3201 dc_nc_3202 dc_nc_3203 dc_nc_3204 dc_nc_3205 dc_nc_3206 dc_nc_3207 dc_nc_3208 dc_nc_3209 dc_nc_3210 dc_nc_3211 dc_nc_3212 dc_nc_3213 dc_nc_3214 dc_nc_3215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
