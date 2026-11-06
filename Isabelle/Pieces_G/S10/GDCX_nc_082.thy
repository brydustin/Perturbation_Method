theory GDCX_nc_082
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1312: "gdc_sub None 1312"
  by (gdc_eval gdc_nc_1312)

lemma gdc_nc_1313: "gdc_sub None 1313"
  by (gdc_eval gdc_nc_1313)

lemma gdc_nc_1314: "gdc_sub None 1314"
  by (gdc_eval gdc_nc_1314)

lemma gdc_nc_1315: "gdc_sub None 1315"
  by (gdc_eval gdc_nc_1315)

lemma gdc_nc_1316: "gdc_sub None 1316"
  by (gdc_eval gdc_nc_1316)

lemma gdc_nc_1317: "gdc_sub None 1317"
  by (gdc_eval gdc_nc_1317)

lemma gdc_nc_1318: "gdc_sub None 1318"
  by (gdc_eval gdc_nc_1318)

lemma gdc_nc_1319: "gdc_sub None 1319"
  by (gdc_eval gdc_nc_1319)

lemma gdc_nc_1320: "gdc_sub None 1320"
  by (gdc_eval gdc_nc_1320)

lemma gdc_nc_1321: "gdc_sub None 1321"
  by (gdc_eval gdc_nc_1321)

lemma gdc_nc_1322: "gdc_sub None 1322"
  by (gdc_eval gdc_nc_1322)

lemma gdc_nc_1323: "gdc_sub None 1323"
  by (gdc_eval gdc_nc_1323)

lemma gdc_nc_1324: "gdc_sub None 1324"
  by (gdc_eval gdc_nc_1324)

lemma gdc_nc_1325: "gdc_sub None 1325"
  by (gdc_eval gdc_nc_1325)

lemma gdc_nc_1326: "gdc_sub None 1326"
  by (gdc_eval gdc_nc_1326)

lemma gdc_nc_1327: "gdc_sub None 1327"
  by (gdc_eval gdc_nc_1327)

lemma gupt_nc_082: "[1312..<1328] = [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]"
  by (simp add: upt_rec)

lemma gsec_nc_082: "\<forall>j\<in>{16 * 82..<16 * 82 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 82..<16 * 82 + 16}"
  then have "j \<in> set [1312..<1328]" unfolding set_upt by simp
  then have "j \<in> set [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]" unfolding gupt_nc_082 .
  then show "gdc_sub None j" using gdc_nc_1312 gdc_nc_1313 gdc_nc_1314 gdc_nc_1315 gdc_nc_1316 gdc_nc_1317 gdc_nc_1318 gdc_nc_1319 gdc_nc_1320 gdc_nc_1321 gdc_nc_1322 gdc_nc_1323 gdc_nc_1324 gdc_nc_1325 gdc_nc_1326 gdc_nc_1327
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
