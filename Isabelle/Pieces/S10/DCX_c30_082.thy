theory DCX_c30_082
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1312: "dc_sub dc_b30 1312"
  by (dc_eval dc_c30_1312)

lemma dc_c30_1313: "dc_sub dc_b30 1313"
  by (dc_eval dc_c30_1313)

lemma dc_c30_1314: "dc_sub dc_b30 1314"
  by (dc_eval dc_c30_1314)

lemma dc_c30_1315: "dc_sub dc_b30 1315"
  by (dc_eval dc_c30_1315)

lemma dc_c30_1316: "dc_sub dc_b30 1316"
  by (dc_eval dc_c30_1316)

lemma dc_c30_1317: "dc_sub dc_b30 1317"
  by (dc_eval dc_c30_1317)

lemma dc_c30_1318: "dc_sub dc_b30 1318"
  by (dc_eval dc_c30_1318)

lemma dc_c30_1319: "dc_sub dc_b30 1319"
  by (dc_eval dc_c30_1319)

lemma dc_c30_1320: "dc_sub dc_b30 1320"
  by (dc_eval dc_c30_1320)

lemma dc_c30_1321: "dc_sub dc_b30 1321"
  by (dc_eval dc_c30_1321)

lemma dc_c30_1322: "dc_sub dc_b30 1322"
  by (dc_eval dc_c30_1322)

lemma dc_c30_1323: "dc_sub dc_b30 1323"
  by (dc_eval dc_c30_1323)

lemma dc_c30_1324: "dc_sub dc_b30 1324"
  by (dc_eval dc_c30_1324)

lemma dc_c30_1325: "dc_sub dc_b30 1325"
  by (dc_eval dc_c30_1325)

lemma dc_c30_1326: "dc_sub dc_b30 1326"
  by (dc_eval dc_c30_1326)

lemma dc_c30_1327: "dc_sub dc_b30 1327"
  by (dc_eval dc_c30_1327)

lemma upt_c30_082: "[1312..<1328] = [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]"
  by (simp add: upt_rec)

lemma sec_c30_082: "\<forall>j\<in>{16 * 82..<16 * 82 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 82..<16 * 82 + 16}"
  then have "j \<in> set [1312..<1328]" unfolding set_upt by simp
  then have "j \<in> set [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]" unfolding upt_c30_082 .
  then show "dc_sub dc_b30 j" using dc_c30_1312 dc_c30_1313 dc_c30_1314 dc_c30_1315 dc_c30_1316 dc_c30_1317 dc_c30_1318 dc_c30_1319 dc_c30_1320 dc_c30_1321 dc_c30_1322 dc_c30_1323 dc_c30_1324 dc_c30_1325 dc_c30_1326 dc_c30_1327
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
