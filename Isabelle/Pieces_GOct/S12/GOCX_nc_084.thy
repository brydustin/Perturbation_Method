theory GOCX_nc_084
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1344: "goc_sub None 1344"
  by (goc_eval goc_nc_1344)

lemma goc_nc_1345: "goc_sub None 1345"
  by (goc_eval goc_nc_1345)

lemma goc_nc_1346: "goc_sub None 1346"
  by (goc_eval goc_nc_1346)

lemma goc_nc_1347: "goc_sub None 1347"
  by (goc_eval goc_nc_1347)

lemma goc_nc_1348: "goc_sub None 1348"
  by (goc_eval goc_nc_1348)

lemma goc_nc_1349: "goc_sub None 1349"
  by (goc_eval goc_nc_1349)

lemma goc_nc_1350: "goc_sub None 1350"
  by (goc_eval goc_nc_1350)

lemma goc_nc_1351: "goc_sub None 1351"
  by (goc_eval goc_nc_1351)

lemma goc_nc_1352: "goc_sub None 1352"
  by (goc_eval goc_nc_1352)

lemma goc_nc_1353: "goc_sub None 1353"
  by (goc_eval goc_nc_1353)

lemma goc_nc_1354: "goc_sub None 1354"
  by (goc_eval goc_nc_1354)

lemma goc_nc_1355: "goc_sub None 1355"
  by (goc_eval goc_nc_1355)

lemma goc_nc_1356: "goc_sub None 1356"
  by (goc_eval goc_nc_1356)

lemma goc_nc_1357: "goc_sub None 1357"
  by (goc_eval goc_nc_1357)

lemma goc_nc_1358: "goc_sub None 1358"
  by (goc_eval goc_nc_1358)

lemma goc_nc_1359: "goc_sub None 1359"
  by (goc_eval goc_nc_1359)

lemma gupt_nc_084: "[1344..<1360] = [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]"
  by (simp add: upt_rec)

lemma gsec_nc_084: "\<forall>j\<in>{16 * 84..<16 * 84 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 84..<16 * 84 + 16}"
  then have "j \<in> set [1344..<1360]" unfolding set_upt by simp
  then have "j \<in> set [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]" unfolding gupt_nc_084 .
  then show "goc_sub None j" using goc_nc_1344 goc_nc_1345 goc_nc_1346 goc_nc_1347 goc_nc_1348 goc_nc_1349 goc_nc_1350 goc_nc_1351 goc_nc_1352 goc_nc_1353 goc_nc_1354 goc_nc_1355 goc_nc_1356 goc_nc_1357 goc_nc_1358 goc_nc_1359
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
