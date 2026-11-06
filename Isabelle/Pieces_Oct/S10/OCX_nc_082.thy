theory OCX_nc_082
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1312: "oc_sub None 1312"
  by (oc_eval oc_nc_1312)

lemma oc_nc_1313: "oc_sub None 1313"
  by (oc_eval oc_nc_1313)

lemma oc_nc_1314: "oc_sub None 1314"
  by (oc_eval oc_nc_1314)

lemma oc_nc_1315: "oc_sub None 1315"
  by (oc_eval oc_nc_1315)

lemma oc_nc_1316: "oc_sub None 1316"
  by (oc_eval oc_nc_1316)

lemma oc_nc_1317: "oc_sub None 1317"
  by (oc_eval oc_nc_1317)

lemma oc_nc_1318: "oc_sub None 1318"
  by (oc_eval oc_nc_1318)

lemma oc_nc_1319: "oc_sub None 1319"
  by (oc_eval oc_nc_1319)

lemma oc_nc_1320: "oc_sub None 1320"
  by (oc_eval oc_nc_1320)

lemma oc_nc_1321: "oc_sub None 1321"
  by (oc_eval oc_nc_1321)

lemma oc_nc_1322: "oc_sub None 1322"
  by (oc_eval oc_nc_1322)

lemma oc_nc_1323: "oc_sub None 1323"
  by (oc_eval oc_nc_1323)

lemma oc_nc_1324: "oc_sub None 1324"
  by (oc_eval oc_nc_1324)

lemma oc_nc_1325: "oc_sub None 1325"
  by (oc_eval oc_nc_1325)

lemma oc_nc_1326: "oc_sub None 1326"
  by (oc_eval oc_nc_1326)

lemma oc_nc_1327: "oc_sub None 1327"
  by (oc_eval oc_nc_1327)

lemma upt_nc_082: "[1312..<1328] = [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]"
  by (simp add: upt_rec)

lemma sec_nc_082: "\<forall>j\<in>{16 * 82..<16 * 82 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 82..<16 * 82 + 16}"
  then have "j \<in> set [1312..<1328]" unfolding set_upt by simp
  then have "j \<in> set [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]" unfolding upt_nc_082 .
  then show "oc_sub None j" using oc_nc_1312 oc_nc_1313 oc_nc_1314 oc_nc_1315 oc_nc_1316 oc_nc_1317 oc_nc_1318 oc_nc_1319 oc_nc_1320 oc_nc_1321 oc_nc_1322 oc_nc_1323 oc_nc_1324 oc_nc_1325 oc_nc_1326 oc_nc_1327
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
