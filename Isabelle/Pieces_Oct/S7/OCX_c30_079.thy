theory OCX_c30_079
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1264: "oc_sub oc_b30 1264"
  by (oc_eval oc_c30_1264)

lemma oc_c30_1265: "oc_sub oc_b30 1265"
  by (oc_eval oc_c30_1265)

lemma oc_c30_1266: "oc_sub oc_b30 1266"
  by (oc_eval oc_c30_1266)

lemma oc_c30_1267: "oc_sub oc_b30 1267"
  by (oc_eval oc_c30_1267)

lemma oc_c30_1268: "oc_sub oc_b30 1268"
  by (oc_eval oc_c30_1268)

lemma oc_c30_1269: "oc_sub oc_b30 1269"
  by (oc_eval oc_c30_1269)

lemma oc_c30_1270: "oc_sub oc_b30 1270"
  by (oc_eval oc_c30_1270)

lemma oc_c30_1271: "oc_sub oc_b30 1271"
  by (oc_eval oc_c30_1271)

lemma oc_c30_1272: "oc_sub oc_b30 1272"
  by (oc_eval oc_c30_1272)

lemma oc_c30_1273: "oc_sub oc_b30 1273"
  by (oc_eval oc_c30_1273)

lemma oc_c30_1274: "oc_sub oc_b30 1274"
  by (oc_eval oc_c30_1274)

lemma oc_c30_1275: "oc_sub oc_b30 1275"
  by (oc_eval oc_c30_1275)

lemma oc_c30_1276: "oc_sub oc_b30 1276"
  by (oc_eval oc_c30_1276)

lemma oc_c30_1277: "oc_sub oc_b30 1277"
  by (oc_eval oc_c30_1277)

lemma oc_c30_1278: "oc_sub oc_b30 1278"
  by (oc_eval oc_c30_1278)

lemma oc_c30_1279: "oc_sub oc_b30 1279"
  by (oc_eval oc_c30_1279)

lemma upt_c30_079: "[1264..<1280] = [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]"
  by (simp add: upt_rec)

lemma sec_c30_079: "\<forall>j\<in>{16 * 79..<16 * 79 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 79..<16 * 79 + 16}"
  then have "j \<in> set [1264..<1280]" unfolding set_upt by simp
  then have "j \<in> set [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]" unfolding upt_c30_079 .
  then show "oc_sub oc_b30 j" using oc_c30_1264 oc_c30_1265 oc_c30_1266 oc_c30_1267 oc_c30_1268 oc_c30_1269 oc_c30_1270 oc_c30_1271 oc_c30_1272 oc_c30_1273 oc_c30_1274 oc_c30_1275 oc_c30_1276 oc_c30_1277 oc_c30_1278 oc_c30_1279
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
