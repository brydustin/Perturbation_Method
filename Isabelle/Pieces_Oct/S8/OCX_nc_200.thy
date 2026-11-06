theory OCX_nc_200
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_3200: "oc_sub None 3200"
  by (oc_eval oc_nc_3200)

lemma oc_nc_3201: "oc_sub None 3201"
  by (oc_eval oc_nc_3201)

lemma oc_nc_3202: "oc_sub None 3202"
  by (oc_eval oc_nc_3202)

lemma oc_nc_3203: "oc_sub None 3203"
  by (oc_eval oc_nc_3203)

lemma oc_nc_3204: "oc_sub None 3204"
  by (oc_eval oc_nc_3204)

lemma oc_nc_3205: "oc_sub None 3205"
  by (oc_eval oc_nc_3205)

lemma oc_nc_3206: "oc_sub None 3206"
  by (oc_eval oc_nc_3206)

lemma oc_nc_3207: "oc_sub None 3207"
  by (oc_eval oc_nc_3207)

lemma oc_nc_3208: "oc_sub None 3208"
  by (oc_eval oc_nc_3208)

lemma oc_nc_3209: "oc_sub None 3209"
  by (oc_eval oc_nc_3209)

lemma oc_nc_3210: "oc_sub None 3210"
  by (oc_eval oc_nc_3210)

lemma oc_nc_3211: "oc_sub None 3211"
  by (oc_eval oc_nc_3211)

lemma oc_nc_3212: "oc_sub None 3212"
  by (oc_eval oc_nc_3212)

lemma oc_nc_3213: "oc_sub None 3213"
  by (oc_eval oc_nc_3213)

lemma oc_nc_3214: "oc_sub None 3214"
  by (oc_eval oc_nc_3214)

lemma oc_nc_3215: "oc_sub None 3215"
  by (oc_eval oc_nc_3215)

lemma upt_nc_200: "[3200..<3216] = [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]"
  by (simp add: upt_rec)

lemma sec_nc_200: "\<forall>j\<in>{16 * 200..<16 * 200 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 200..<16 * 200 + 16}"
  then have "j \<in> set [3200..<3216]" unfolding set_upt by simp
  then have "j \<in> set [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]" unfolding upt_nc_200 .
  then show "oc_sub None j" using oc_nc_3200 oc_nc_3201 oc_nc_3202 oc_nc_3203 oc_nc_3204 oc_nc_3205 oc_nc_3206 oc_nc_3207 oc_nc_3208 oc_nc_3209 oc_nc_3210 oc_nc_3211 oc_nc_3212 oc_nc_3213 oc_nc_3214 oc_nc_3215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
