theory GDCX_nc_075
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1200: "gdc_sub None 1200"
  by (gdc_eval gdc_nc_1200)

lemma gdc_nc_1201: "gdc_sub None 1201"
  by (gdc_eval gdc_nc_1201)

lemma gdc_nc_1202: "gdc_sub None 1202"
  by (gdc_eval gdc_nc_1202)

lemma gdc_nc_1203: "gdc_sub None 1203"
  by (gdc_eval gdc_nc_1203)

lemma gdc_nc_1204: "gdc_sub None 1204"
  by (gdc_eval gdc_nc_1204)

lemma gdc_nc_1205: "gdc_sub None 1205"
  by (gdc_eval gdc_nc_1205)

lemma gdc_nc_1206: "gdc_sub None 1206"
  by (gdc_eval gdc_nc_1206)

lemma gdc_nc_1207: "gdc_sub None 1207"
  by (gdc_eval gdc_nc_1207)

lemma gdc_nc_1208: "gdc_sub None 1208"
  by (gdc_eval gdc_nc_1208)

lemma gdc_nc_1209: "gdc_sub None 1209"
  by (gdc_eval gdc_nc_1209)

lemma gdc_nc_1210: "gdc_sub None 1210"
  by (gdc_eval gdc_nc_1210)

lemma gdc_nc_1211: "gdc_sub None 1211"
  by (gdc_eval gdc_nc_1211)

lemma gdc_nc_1212: "gdc_sub None 1212"
  by (gdc_eval gdc_nc_1212)

lemma gdc_nc_1213: "gdc_sub None 1213"
  by (gdc_eval gdc_nc_1213)

lemma gdc_nc_1214: "gdc_sub None 1214"
  by (gdc_eval gdc_nc_1214)

lemma gdc_nc_1215: "gdc_sub None 1215"
  by (gdc_eval gdc_nc_1215)

lemma gupt_nc_075: "[1200..<1216] = [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]"
  by (simp add: upt_rec)

lemma gsec_nc_075: "\<forall>j\<in>{16 * 75..<16 * 75 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 75..<16 * 75 + 16}"
  then have "j \<in> set [1200..<1216]" unfolding set_upt by simp
  then have "j \<in> set [1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215]" unfolding gupt_nc_075 .
  then show "gdc_sub None j" using gdc_nc_1200 gdc_nc_1201 gdc_nc_1202 gdc_nc_1203 gdc_nc_1204 gdc_nc_1205 gdc_nc_1206 gdc_nc_1207 gdc_nc_1208 gdc_nc_1209 gdc_nc_1210 gdc_nc_1211 gdc_nc_1212 gdc_nc_1213 gdc_nc_1214 gdc_nc_1215
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
