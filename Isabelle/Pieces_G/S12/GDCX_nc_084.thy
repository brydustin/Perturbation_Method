theory GDCX_nc_084
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1344: "gdc_sub None 1344"
  by (gdc_eval gdc_nc_1344)

lemma gdc_nc_1345: "gdc_sub None 1345"
  by (gdc_eval gdc_nc_1345)

lemma gdc_nc_1346: "gdc_sub None 1346"
  by (gdc_eval gdc_nc_1346)

lemma gdc_nc_1347: "gdc_sub None 1347"
  by (gdc_eval gdc_nc_1347)

lemma gdc_nc_1348: "gdc_sub None 1348"
  by (gdc_eval gdc_nc_1348)

lemma gdc_nc_1349: "gdc_sub None 1349"
  by (gdc_eval gdc_nc_1349)

lemma gdc_nc_1350: "gdc_sub None 1350"
  by (gdc_eval gdc_nc_1350)

lemma gdc_nc_1351: "gdc_sub None 1351"
  by (gdc_eval gdc_nc_1351)

lemma gdc_nc_1352: "gdc_sub None 1352"
  by (gdc_eval gdc_nc_1352)

lemma gdc_nc_1353: "gdc_sub None 1353"
  by (gdc_eval gdc_nc_1353)

lemma gdc_nc_1354: "gdc_sub None 1354"
  by (gdc_eval gdc_nc_1354)

lemma gdc_nc_1355: "gdc_sub None 1355"
  by (gdc_eval gdc_nc_1355)

lemma gdc_nc_1356: "gdc_sub None 1356"
  by (gdc_eval gdc_nc_1356)

lemma gdc_nc_1357: "gdc_sub None 1357"
  by (gdc_eval gdc_nc_1357)

lemma gdc_nc_1358: "gdc_sub None 1358"
  by (gdc_eval gdc_nc_1358)

lemma gdc_nc_1359: "gdc_sub None 1359"
  by (gdc_eval gdc_nc_1359)

lemma gupt_nc_084: "[1344..<1360] = [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]"
  by (simp add: upt_rec)

lemma gsec_nc_084: "\<forall>j\<in>{16 * 84..<16 * 84 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 84..<16 * 84 + 16}"
  then have "j \<in> set [1344..<1360]" unfolding set_upt by simp
  then have "j \<in> set [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]" unfolding gupt_nc_084 .
  then show "gdc_sub None j" using gdc_nc_1344 gdc_nc_1345 gdc_nc_1346 gdc_nc_1347 gdc_nc_1348 gdc_nc_1349 gdc_nc_1350 gdc_nc_1351 gdc_nc_1352 gdc_nc_1353 gdc_nc_1354 gdc_nc_1355 gdc_nc_1356 gdc_nc_1357 gdc_nc_1358 gdc_nc_1359
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
