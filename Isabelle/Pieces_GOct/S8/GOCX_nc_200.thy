theory GOCX_nc_200
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3200: "goc_sub None 3200"
  by (goc_eval goc_nc_3200)

lemma goc_nc_3201: "goc_sub None 3201"
  by (goc_eval goc_nc_3201)

lemma goc_nc_3202: "goc_sub None 3202"
  by (goc_eval goc_nc_3202)

lemma goc_nc_3203: "goc_sub None 3203"
  by (goc_eval goc_nc_3203)

lemma goc_nc_3204: "goc_sub None 3204"
  by (goc_eval goc_nc_3204)

lemma goc_nc_3205: "goc_sub None 3205"
  by (goc_eval goc_nc_3205)

lemma goc_nc_3206: "goc_sub None 3206"
  by (goc_eval goc_nc_3206)

lemma goc_nc_3207: "goc_sub None 3207"
  by (goc_eval goc_nc_3207)

lemma goc_nc_3208: "goc_sub None 3208"
  by (goc_eval goc_nc_3208)

lemma goc_nc_3209: "goc_sub None 3209"
  by (goc_eval goc_nc_3209)

lemma goc_nc_3210: "goc_sub None 3210"
  by (goc_eval goc_nc_3210)

lemma goc_nc_3211: "goc_sub None 3211"
  by (goc_eval goc_nc_3211)

lemma goc_nc_3212: "goc_sub None 3212"
  by (goc_eval goc_nc_3212)

lemma goc_nc_3213: "goc_sub None 3213"
  by (goc_eval goc_nc_3213)

lemma goc_nc_3214: "goc_sub None 3214"
  by (goc_eval goc_nc_3214)

lemma goc_nc_3215: "goc_sub None 3215"
  by (goc_eval goc_nc_3215)

lemma gupt_nc_200: "[3200..<3216] = [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]"
  by (simp add: upt_rec)

lemma gsec_nc_200: "\<forall>j\<in>{16 * 200..<16 * 200 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 200..<16 * 200 + 16}"
  then have "j \<in> set [3200..<3216]" unfolding set_upt by simp
  then have "j \<in> set [3200, 3201, 3202, 3203, 3204, 3205, 3206, 3207, 3208, 3209, 3210, 3211, 3212, 3213, 3214, 3215]" unfolding gupt_nc_200 .
  then show "goc_sub None j" using goc_nc_3200 goc_nc_3201 goc_nc_3202 goc_nc_3203 goc_nc_3204 goc_nc_3205 goc_nc_3206 goc_nc_3207 goc_nc_3208 goc_nc_3209 goc_nc_3210 goc_nc_3211 goc_nc_3212 goc_nc_3213 goc_nc_3214 goc_nc_3215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
