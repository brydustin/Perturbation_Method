theory OCX_c30_082
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1312: "oc_sub oc_b30 1312"
  by (oc_eval oc_c30_1312)

lemma oc_c30_1313: "oc_sub oc_b30 1313"
  by (oc_eval oc_c30_1313)

lemma oc_c30_1314: "oc_sub oc_b30 1314"
  by (oc_eval oc_c30_1314)

lemma oc_c30_1315: "oc_sub oc_b30 1315"
  by (oc_eval oc_c30_1315)

lemma oc_c30_1316: "oc_sub oc_b30 1316"
  by (oc_eval oc_c30_1316)

lemma oc_c30_1317: "oc_sub oc_b30 1317"
  by (oc_eval oc_c30_1317)

lemma oc_c30_1318: "oc_sub oc_b30 1318"
  by (oc_eval oc_c30_1318)

lemma oc_c30_1319: "oc_sub oc_b30 1319"
  by (oc_eval oc_c30_1319)

lemma oc_c30_1320: "oc_sub oc_b30 1320"
  by (oc_eval oc_c30_1320)

lemma oc_c30_1321: "oc_sub oc_b30 1321"
  by (oc_eval oc_c30_1321)

lemma oc_c30_1322: "oc_sub oc_b30 1322"
  by (oc_eval oc_c30_1322)

lemma oc_c30_1323: "oc_sub oc_b30 1323"
  by (oc_eval oc_c30_1323)

lemma oc_c30_1324: "oc_sub oc_b30 1324"
  by (oc_eval oc_c30_1324)

lemma oc_c30_1325: "oc_sub oc_b30 1325"
  by (oc_eval oc_c30_1325)

lemma oc_c30_1326: "oc_sub oc_b30 1326"
  by (oc_eval oc_c30_1326)

lemma oc_c30_1327: "oc_sub oc_b30 1327"
  by (oc_eval oc_c30_1327)

lemma upt_c30_082: "[1312..<1328] = [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]"
  by (simp add: upt_rec)

lemma sec_c30_082: "\<forall>j\<in>{16 * 82..<16 * 82 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 82..<16 * 82 + 16}"
  then have "j \<in> set [1312..<1328]" unfolding set_upt by simp
  then have "j \<in> set [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]" unfolding upt_c30_082 .
  then show "oc_sub oc_b30 j" using oc_c30_1312 oc_c30_1313 oc_c30_1314 oc_c30_1315 oc_c30_1316 oc_c30_1317 oc_c30_1318 oc_c30_1319 oc_c30_1320 oc_c30_1321 oc_c30_1322 oc_c30_1323 oc_c30_1324 oc_c30_1325 oc_c30_1326 oc_c30_1327
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
