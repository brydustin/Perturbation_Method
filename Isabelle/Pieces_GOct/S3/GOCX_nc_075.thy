theory GOCX_nc_075
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1200: "goc_sub None 1200"
  by (goc_eval goc_nc_1200)

lemma goc_nc_1201: "goc_sub None 1201"
  by (goc_eval goc_nc_1201)

lemma goc_nc_1202: "goc_sub None 1202"
  by (goc_eval goc_nc_1202)

lemma goc_nc_1203: "goc_sub None 1203"
  by (goc_eval goc_nc_1203)

lemma goc_nc_1204: "goc_sub None 1204"
  by (goc_eval goc_nc_1204)

lemma goc_nc_1205: "goc_sub None 1205"
  by (goc_eval goc_nc_1205)

lemma goc_nc_1206: "goc_sub None 1206"
  by (goc_eval goc_nc_1206)

lemma goc_nc_1207: "goc_sub None 1207"
  by (goc_eval goc_nc_1207)

lemma goc_nc_1208: "goc_sub None 1208"
  by (goc_eval goc_nc_1208)

lemma goc_nc_1209: "goc_sub None 1209"
  by (goc_eval goc_nc_1209)

lemma goc_nc_1210: "goc_sub None 1210"
  by (goc_eval goc_nc_1210)

lemma goc_nc_1211: "goc_sub None 1211"
  by (goc_eval goc_nc_1211)

lemma goc_nc_1212: "goc_sub None 1212"
  by (goc_eval goc_nc_1212)

lemma goc_nc_1213: "goc_sub None 1213"
  by (goc_eval goc_nc_1213)

lemma goc_nc_1214: "goc_sub None 1214"
  by (goc_eval goc_nc_1214)

lemma goc_nc_1215: "goc_sub None 1215"
  by (goc_eval goc_nc_1215)

lemma gupt_nc_075: "[1200..<1216] = [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]"
  by (simp add: upt_rec)

lemma gsec_nc_075: "\<forall>j\<in>{16 * 75..<16 * 75 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 75..<16 * 75 + 16}"
  then have "j \<in> set [1200..<1216]" unfolding set_upt by simp
  then have "j \<in> set [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]" unfolding gupt_nc_075 .
  then show "goc_sub None j" using goc_nc_1200 goc_nc_1201 goc_nc_1202 goc_nc_1203 goc_nc_1204 goc_nc_1205 goc_nc_1206 goc_nc_1207 goc_nc_1208 goc_nc_1209 goc_nc_1210 goc_nc_1211 goc_nc_1212 goc_nc_1213 goc_nc_1214 goc_nc_1215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
