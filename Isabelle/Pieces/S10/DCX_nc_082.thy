theory DCX_nc_082
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1312: "dc_sub None 1312"
  by (dc_eval dc_nc_1312)

lemma dc_nc_1313: "dc_sub None 1313"
  by (dc_eval dc_nc_1313)

lemma dc_nc_1314: "dc_sub None 1314"
  by (dc_eval dc_nc_1314)

lemma dc_nc_1315: "dc_sub None 1315"
  by (dc_eval dc_nc_1315)

lemma dc_nc_1316: "dc_sub None 1316"
  by (dc_eval dc_nc_1316)

lemma dc_nc_1317: "dc_sub None 1317"
  by (dc_eval dc_nc_1317)

lemma dc_nc_1318: "dc_sub None 1318"
  by (dc_eval dc_nc_1318)

lemma dc_nc_1319: "dc_sub None 1319"
  by (dc_eval dc_nc_1319)

lemma dc_nc_1320: "dc_sub None 1320"
  by (dc_eval dc_nc_1320)

lemma dc_nc_1321: "dc_sub None 1321"
  by (dc_eval dc_nc_1321)

lemma dc_nc_1322: "dc_sub None 1322"
  by (dc_eval dc_nc_1322)

lemma dc_nc_1323: "dc_sub None 1323"
  by (dc_eval dc_nc_1323)

lemma dc_nc_1324: "dc_sub None 1324"
  by (dc_eval dc_nc_1324)

lemma dc_nc_1325: "dc_sub None 1325"
  by (dc_eval dc_nc_1325)

lemma dc_nc_1326: "dc_sub None 1326"
  by (dc_eval dc_nc_1326)

lemma dc_nc_1327: "dc_sub None 1327"
  by (dc_eval dc_nc_1327)

lemma upt_nc_082: "[1312..<1328] = [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]"
  by (simp add: upt_rec)

lemma sec_nc_082: "\<forall>j\<in>{16 * 82..<16 * 82 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 82..<16 * 82 + 16}"
  then have "j \<in> set [1312..<1328]" unfolding set_upt by simp
  then have "j \<in> set [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]" unfolding upt_nc_082 .
  then show "dc_sub None j" using dc_nc_1312 dc_nc_1313 dc_nc_1314 dc_nc_1315 dc_nc_1316 dc_nc_1317 dc_nc_1318 dc_nc_1319 dc_nc_1320 dc_nc_1321 dc_nc_1322 dc_nc_1323 dc_nc_1324 dc_nc_1325 dc_nc_1326 dc_nc_1327
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
