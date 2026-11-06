theory GOCX_nc_079
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1264: "goc_sub None 1264"
  by (goc_eval goc_nc_1264)

lemma goc_nc_1265: "goc_sub None 1265"
  by (goc_eval goc_nc_1265)

lemma goc_nc_1266: "goc_sub None 1266"
  by (goc_eval goc_nc_1266)

lemma goc_nc_1267: "goc_sub None 1267"
  by (goc_eval goc_nc_1267)

lemma goc_nc_1268: "goc_sub None 1268"
  by (goc_eval goc_nc_1268)

lemma goc_nc_1269: "goc_sub None 1269"
  by (goc_eval goc_nc_1269)

lemma goc_nc_1270: "goc_sub None 1270"
  by (goc_eval goc_nc_1270)

lemma goc_nc_1271: "goc_sub None 1271"
  by (goc_eval goc_nc_1271)

lemma goc_nc_1272: "goc_sub None 1272"
  by (goc_eval goc_nc_1272)

lemma goc_nc_1273: "goc_sub None 1273"
  by (goc_eval goc_nc_1273)

lemma goc_nc_1274: "goc_sub None 1274"
  by (goc_eval goc_nc_1274)

lemma goc_nc_1275: "goc_sub None 1275"
  by (goc_eval goc_nc_1275)

lemma goc_nc_1276: "goc_sub None 1276"
  by (goc_eval goc_nc_1276)

lemma goc_nc_1277: "goc_sub None 1277"
  by (goc_eval goc_nc_1277)

lemma goc_nc_1278: "goc_sub None 1278"
  by (goc_eval goc_nc_1278)

lemma goc_nc_1279: "goc_sub None 1279"
  by (goc_eval goc_nc_1279)

lemma gupt_nc_079: "[1264..<1280] = [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]"
  by (simp add: upt_rec)

lemma gsec_nc_079: "\<forall>j\<in>{16 * 79..<16 * 79 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 79..<16 * 79 + 16}"
  then have "j \<in> set [1264..<1280]" unfolding set_upt by simp
  then have "j \<in> set [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]" unfolding gupt_nc_079 .
  then show "goc_sub None j" using goc_nc_1264 goc_nc_1265 goc_nc_1266 goc_nc_1267 goc_nc_1268 goc_nc_1269 goc_nc_1270 goc_nc_1271 goc_nc_1272 goc_nc_1273 goc_nc_1274 goc_nc_1275 goc_nc_1276 goc_nc_1277 goc_nc_1278 goc_nc_1279
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
