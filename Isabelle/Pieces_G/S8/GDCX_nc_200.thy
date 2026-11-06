theory GDCX_nc_200
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3200: "gdc_sub None 3200"
  by (gdc_eval gdc_nc_3200)

lemma gdc_nc_3201: "gdc_sub None 3201"
  by (gdc_eval gdc_nc_3201)

lemma gdc_nc_3202: "gdc_sub None 3202"
  by (gdc_eval gdc_nc_3202)

lemma gdc_nc_3203: "gdc_sub None 3203"
  by (gdc_eval gdc_nc_3203)

lemma gdc_nc_3204: "gdc_sub None 3204"
  by (gdc_eval gdc_nc_3204)

lemma gdc_nc_3205: "gdc_sub None 3205"
  by (gdc_eval gdc_nc_3205)

lemma gdc_nc_3206: "gdc_sub None 3206"
  by (gdc_eval gdc_nc_3206)

lemma gdc_nc_3207: "gdc_sub None 3207"
  by (gdc_eval gdc_nc_3207)

lemma gdc_nc_3208: "gdc_sub None 3208"
  by (gdc_eval gdc_nc_3208)

lemma gdc_nc_3209: "gdc_sub None 3209"
  by (gdc_eval gdc_nc_3209)

lemma gdc_nc_3210: "gdc_sub None 3210"
  by (gdc_eval gdc_nc_3210)

lemma gdc_nc_3211: "gdc_sub None 3211"
  by (gdc_eval gdc_nc_3211)

lemma gdc_nc_3212: "gdc_sub None 3212"
  by (gdc_eval gdc_nc_3212)

lemma gdc_nc_3213: "gdc_sub None 3213"
  by (gdc_eval gdc_nc_3213)

lemma gdc_nc_3214: "gdc_sub None 3214"
  by (gdc_eval gdc_nc_3214)

lemma gdc_nc_3215: "gdc_sub None 3215"
  by (gdc_eval gdc_nc_3215)

lemma gupt_nc_200: "[3200..<3216] = [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]"
  by (simp add: upt_rec)

lemma gsec_nc_200: "\<forall>j\<in>{16 * 200..<16 * 200 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 200..<16 * 200 + 16}"
  then have "j \<in> set [3200..<3216]" unfolding set_upt by simp
  then have "j \<in> set [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]" unfolding gupt_nc_200 .
  then show "gdc_sub None j" using gdc_nc_3200 gdc_nc_3201 gdc_nc_3202 gdc_nc_3203 gdc_nc_3204 gdc_nc_3205 gdc_nc_3206 gdc_nc_3207 gdc_nc_3208 gdc_nc_3209 gdc_nc_3210 gdc_nc_3211 gdc_nc_3212 gdc_nc_3213 gdc_nc_3214 gdc_nc_3215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
