theory DCX_nc_079
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1264: "dc_sub None 1264"
  by (dc_eval dc_nc_1264)

lemma dc_nc_1265: "dc_sub None 1265"
  by (dc_eval dc_nc_1265)

lemma dc_nc_1266: "dc_sub None 1266"
  by (dc_eval dc_nc_1266)

lemma dc_nc_1267: "dc_sub None 1267"
  by (dc_eval dc_nc_1267)

lemma dc_nc_1268: "dc_sub None 1268"
  by (dc_eval dc_nc_1268)

lemma dc_nc_1269: "dc_sub None 1269"
  by (dc_eval dc_nc_1269)

lemma dc_nc_1270: "dc_sub None 1270"
  by (dc_eval dc_nc_1270)

lemma dc_nc_1271: "dc_sub None 1271"
  by (dc_eval dc_nc_1271)

lemma dc_nc_1272: "dc_sub None 1272"
  by (dc_eval dc_nc_1272)

lemma dc_nc_1273: "dc_sub None 1273"
  by (dc_eval dc_nc_1273)

lemma dc_nc_1274: "dc_sub None 1274"
  by (dc_eval dc_nc_1274)

lemma dc_nc_1275: "dc_sub None 1275"
  by (dc_eval dc_nc_1275)

lemma dc_nc_1276: "dc_sub None 1276"
  by (dc_eval dc_nc_1276)

lemma dc_nc_1277: "dc_sub None 1277"
  by (dc_eval dc_nc_1277)

lemma dc_nc_1278: "dc_sub None 1278"
  by (dc_eval dc_nc_1278)

lemma dc_nc_1279: "dc_sub None 1279"
  by (dc_eval dc_nc_1279)

lemma upt_nc_079: "[1264..<1280] = [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]"
  by (simp add: upt_rec)

lemma sec_nc_079: "\<forall>j\<in>{16 * 79..<16 * 79 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 79..<16 * 79 + 16}"
  then have "j \<in> set [1264..<1280]" unfolding set_upt by simp
  then have "j \<in> set [1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279]" unfolding upt_nc_079 .
  then show "dc_sub None j" using dc_nc_1264 dc_nc_1265 dc_nc_1266 dc_nc_1267 dc_nc_1268 dc_nc_1269 dc_nc_1270 dc_nc_1271 dc_nc_1272 dc_nc_1273 dc_nc_1274 dc_nc_1275 dc_nc_1276 dc_nc_1277 dc_nc_1278 dc_nc_1279
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
