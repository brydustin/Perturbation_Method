theory DCX_c30_084
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1344: "dc_sub dc_b30 1344"
  by (dc_eval dc_c30_1344)

lemma dc_c30_1345: "dc_sub dc_b30 1345"
  by (dc_eval dc_c30_1345)

lemma dc_c30_1346: "dc_sub dc_b30 1346"
  by (dc_eval dc_c30_1346)

lemma dc_c30_1347: "dc_sub dc_b30 1347"
  by (dc_eval dc_c30_1347)

lemma dc_c30_1348: "dc_sub dc_b30 1348"
  by (dc_eval dc_c30_1348)

lemma dc_c30_1349: "dc_sub dc_b30 1349"
  by (dc_eval dc_c30_1349)

lemma dc_c30_1350: "dc_sub dc_b30 1350"
  by (dc_eval dc_c30_1350)

lemma dc_c30_1351: "dc_sub dc_b30 1351"
  by (dc_eval dc_c30_1351)

lemma dc_c30_1352: "dc_sub dc_b30 1352"
  by (dc_eval dc_c30_1352)

lemma dc_c30_1353: "dc_sub dc_b30 1353"
  by (dc_eval dc_c30_1353)

lemma dc_c30_1354: "dc_sub dc_b30 1354"
  by (dc_eval dc_c30_1354)

lemma dc_c30_1355: "dc_sub dc_b30 1355"
  by (dc_eval dc_c30_1355)

lemma dc_c30_1356: "dc_sub dc_b30 1356"
  by (dc_eval dc_c30_1356)

lemma dc_c30_1357: "dc_sub dc_b30 1357"
  by (dc_eval dc_c30_1357)

lemma dc_c30_1358: "dc_sub dc_b30 1358"
  by (dc_eval dc_c30_1358)

lemma dc_c30_1359: "dc_sub dc_b30 1359"
  by (dc_eval dc_c30_1359)

lemma upt_c30_084: "[1344..<1360] = [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]"
  by (simp add: upt_rec)

lemma sec_c30_084: "\<forall>j\<in>{16 * 84..<16 * 84 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 84..<16 * 84 + 16}"
  then have "j \<in> set [1344..<1360]" unfolding set_upt by simp
  then have "j \<in> set [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]" unfolding upt_c30_084 .
  then show "dc_sub dc_b30 j" using dc_c30_1344 dc_c30_1345 dc_c30_1346 dc_c30_1347 dc_c30_1348 dc_c30_1349 dc_c30_1350 dc_c30_1351 dc_c30_1352 dc_c30_1353 dc_c30_1354 dc_c30_1355 dc_c30_1356 dc_c30_1357 dc_c30_1358 dc_c30_1359
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
