theory DCX_c30_079
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1264: "dc_sub dc_b30 1264"
  by (dc_eval dc_c30_1264)

lemma dc_c30_1265: "dc_sub dc_b30 1265"
  by (dc_eval dc_c30_1265)

lemma dc_c30_1266: "dc_sub dc_b30 1266"
  by (dc_eval dc_c30_1266)

lemma dc_c30_1267: "dc_sub dc_b30 1267"
  by (dc_eval dc_c30_1267)

lemma dc_c30_1268: "dc_sub dc_b30 1268"
  by (dc_eval dc_c30_1268)

lemma dc_c30_1269: "dc_sub dc_b30 1269"
  by (dc_eval dc_c30_1269)

lemma dc_c30_1270: "dc_sub dc_b30 1270"
  by (dc_eval dc_c30_1270)

lemma dc_c30_1271: "dc_sub dc_b30 1271"
  by (dc_eval dc_c30_1271)

lemma dc_c30_1272: "dc_sub dc_b30 1272"
  by (dc_eval dc_c30_1272)

lemma dc_c30_1273: "dc_sub dc_b30 1273"
  by (dc_eval dc_c30_1273)

lemma dc_c30_1274: "dc_sub dc_b30 1274"
  by (dc_eval dc_c30_1274)

lemma dc_c30_1275: "dc_sub dc_b30 1275"
  by (dc_eval dc_c30_1275)

lemma dc_c30_1276: "dc_sub dc_b30 1276"
  by (dc_eval dc_c30_1276)

lemma dc_c30_1277: "dc_sub dc_b30 1277"
  by (dc_eval dc_c30_1277)

lemma dc_c30_1278: "dc_sub dc_b30 1278"
  by (dc_eval dc_c30_1278)

lemma dc_c30_1279: "dc_sub dc_b30 1279"
  by (dc_eval dc_c30_1279)

lemma upt_c30_079: "[1264..<1280] = [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]"
  by (simp add: upt_rec)

lemma sec_c30_079: "\<forall>j\<in>{16 * 79..<16 * 79 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 79..<16 * 79 + 16}"
  then have "j \<in> set [1264..<1280]" unfolding set_upt by simp
  then have "j \<in> set [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]" unfolding upt_c30_079 .
  then show "dc_sub dc_b30 j" using dc_c30_1264 dc_c30_1265 dc_c30_1266 dc_c30_1267 dc_c30_1268 dc_c30_1269 dc_c30_1270 dc_c30_1271 dc_c30_1272 dc_c30_1273 dc_c30_1274 dc_c30_1275 dc_c30_1276 dc_c30_1277 dc_c30_1278 dc_c30_1279
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
