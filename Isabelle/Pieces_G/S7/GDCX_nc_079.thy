theory GDCX_nc_079
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1264: "gdc_sub None 1264"
  by (gdc_eval gdc_nc_1264)

lemma gdc_nc_1265: "gdc_sub None 1265"
  by (gdc_eval gdc_nc_1265)

lemma gdc_nc_1266: "gdc_sub None 1266"
  by (gdc_eval gdc_nc_1266)

lemma gdc_nc_1267: "gdc_sub None 1267"
  by (gdc_eval gdc_nc_1267)

lemma gdc_nc_1268: "gdc_sub None 1268"
  by (gdc_eval gdc_nc_1268)

lemma gdc_nc_1269: "gdc_sub None 1269"
  by (gdc_eval gdc_nc_1269)

lemma gdc_nc_1270: "gdc_sub None 1270"
  by (gdc_eval gdc_nc_1270)

lemma gdc_nc_1271: "gdc_sub None 1271"
  by (gdc_eval gdc_nc_1271)

lemma gdc_nc_1272: "gdc_sub None 1272"
  by (gdc_eval gdc_nc_1272)

lemma gdc_nc_1273: "gdc_sub None 1273"
  by (gdc_eval gdc_nc_1273)

lemma gdc_nc_1274: "gdc_sub None 1274"
  by (gdc_eval gdc_nc_1274)

lemma gdc_nc_1275: "gdc_sub None 1275"
  by (gdc_eval gdc_nc_1275)

lemma gdc_nc_1276: "gdc_sub None 1276"
  by (gdc_eval gdc_nc_1276)

lemma gdc_nc_1277: "gdc_sub None 1277"
  by (gdc_eval gdc_nc_1277)

lemma gdc_nc_1278: "gdc_sub None 1278"
  by (gdc_eval gdc_nc_1278)

lemma gdc_nc_1279: "gdc_sub None 1279"
  by (gdc_eval gdc_nc_1279)

lemma gupt_nc_079: "[1264..<1280] = [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]"
  by (simp add: upt_rec)

lemma gsec_nc_079: "\<forall>j\<in>{16 * 79..<16 * 79 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 79..<16 * 79 + 16}"
  then have "j \<in> set [1264..<1280]" unfolding set_upt by simp
  then have "j \<in> set [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]" unfolding gupt_nc_079 .
  then show "gdc_sub None j" using gdc_nc_1264 gdc_nc_1265 gdc_nc_1266 gdc_nc_1267 gdc_nc_1268 gdc_nc_1269 gdc_nc_1270 gdc_nc_1271 gdc_nc_1272 gdc_nc_1273 gdc_nc_1274 gdc_nc_1275 gdc_nc_1276 gdc_nc_1277 gdc_nc_1278 gdc_nc_1279
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
