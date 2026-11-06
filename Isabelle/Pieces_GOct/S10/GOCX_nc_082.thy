theory GOCX_nc_082
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1312: "goc_sub None 1312"
  by (goc_eval goc_nc_1312)

lemma goc_nc_1313: "goc_sub None 1313"
  by (goc_eval goc_nc_1313)

lemma goc_nc_1314: "goc_sub None 1314"
  by (goc_eval goc_nc_1314)

lemma goc_nc_1315: "goc_sub None 1315"
  by (goc_eval goc_nc_1315)

lemma goc_nc_1316: "goc_sub None 1316"
  by (goc_eval goc_nc_1316)

lemma goc_nc_1317: "goc_sub None 1317"
  by (goc_eval goc_nc_1317)

lemma goc_nc_1318: "goc_sub None 1318"
  by (goc_eval goc_nc_1318)

lemma goc_nc_1319: "goc_sub None 1319"
  by (goc_eval goc_nc_1319)

lemma goc_nc_1320: "goc_sub None 1320"
  by (goc_eval goc_nc_1320)

lemma goc_nc_1321: "goc_sub None 1321"
  by (goc_eval goc_nc_1321)

lemma goc_nc_1322: "goc_sub None 1322"
  by (goc_eval goc_nc_1322)

lemma goc_nc_1323: "goc_sub None 1323"
  by (goc_eval goc_nc_1323)

lemma goc_nc_1324: "goc_sub None 1324"
  by (goc_eval goc_nc_1324)

lemma goc_nc_1325: "goc_sub None 1325"
  by (goc_eval goc_nc_1325)

lemma goc_nc_1326: "goc_sub None 1326"
  by (goc_eval goc_nc_1326)

lemma goc_nc_1327: "goc_sub None 1327"
  by (goc_eval goc_nc_1327)

lemma gupt_nc_082: "[1312..<1328] = [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]"
  by (simp add: upt_rec)

lemma gsec_nc_082: "\<forall>j\<in>{16 * 82..<16 * 82 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 82..<16 * 82 + 16}"
  then have "j \<in> set [1312..<1328]" unfolding set_upt by simp
  then have "j \<in> set [1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327]" unfolding gupt_nc_082 .
  then show "goc_sub None j" using goc_nc_1312 goc_nc_1313 goc_nc_1314 goc_nc_1315 goc_nc_1316 goc_nc_1317 goc_nc_1318 goc_nc_1319 goc_nc_1320 goc_nc_1321 goc_nc_1322 goc_nc_1323 goc_nc_1324 goc_nc_1325 goc_nc_1326 goc_nc_1327
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
