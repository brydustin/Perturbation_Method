theory OCX_nc_079
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1264: "oc_sub None 1264"
  by (oc_eval oc_nc_1264)

lemma oc_nc_1265: "oc_sub None 1265"
  by (oc_eval oc_nc_1265)

lemma oc_nc_1266: "oc_sub None 1266"
  by (oc_eval oc_nc_1266)

lemma oc_nc_1267: "oc_sub None 1267"
  by (oc_eval oc_nc_1267)

lemma oc_nc_1268: "oc_sub None 1268"
  by (oc_eval oc_nc_1268)

lemma oc_nc_1269: "oc_sub None 1269"
  by (oc_eval oc_nc_1269)

lemma oc_nc_1270: "oc_sub None 1270"
  by (oc_eval oc_nc_1270)

lemma oc_nc_1271: "oc_sub None 1271"
  by (oc_eval oc_nc_1271)

lemma oc_nc_1272: "oc_sub None 1272"
  by (oc_eval oc_nc_1272)

lemma oc_nc_1273: "oc_sub None 1273"
  by (oc_eval oc_nc_1273)

lemma oc_nc_1274: "oc_sub None 1274"
  by (oc_eval oc_nc_1274)

lemma oc_nc_1275: "oc_sub None 1275"
  by (oc_eval oc_nc_1275)

lemma oc_nc_1276: "oc_sub None 1276"
  by (oc_eval oc_nc_1276)

lemma oc_nc_1277: "oc_sub None 1277"
  by (oc_eval oc_nc_1277)

lemma oc_nc_1278: "oc_sub None 1278"
  by (oc_eval oc_nc_1278)

lemma oc_nc_1279: "oc_sub None 1279"
  by (oc_eval oc_nc_1279)

lemma upt_nc_079: "[1264..<1280] = [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]"
  by (simp add: upt_rec)

lemma sec_nc_079: "\<forall>j\<in>{16 * 79..<16 * 79 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 79..<16 * 79 + 16}"
  then have "j \<in> set [1264..<1280]" unfolding set_upt by simp
  then have "j \<in> set [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]" unfolding upt_nc_079 .
  then show "oc_sub None j" using oc_nc_1264 oc_nc_1265 oc_nc_1266 oc_nc_1267 oc_nc_1268 oc_nc_1269 oc_nc_1270 oc_nc_1271 oc_nc_1272 oc_nc_1273 oc_nc_1274 oc_nc_1275 oc_nc_1276 oc_nc_1277 oc_nc_1278 oc_nc_1279
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
