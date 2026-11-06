theory OCX_c30_084
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1344: "oc_sub oc_b30 1344"
  by (oc_eval oc_c30_1344)

lemma oc_c30_1345: "oc_sub oc_b30 1345"
  by (oc_eval oc_c30_1345)

lemma oc_c30_1346: "oc_sub oc_b30 1346"
  by (oc_eval oc_c30_1346)

lemma oc_c30_1347: "oc_sub oc_b30 1347"
  by (oc_eval oc_c30_1347)

lemma oc_c30_1348: "oc_sub oc_b30 1348"
  by (oc_eval oc_c30_1348)

lemma oc_c30_1349: "oc_sub oc_b30 1349"
  by (oc_eval oc_c30_1349)

lemma oc_c30_1350: "oc_sub oc_b30 1350"
  by (oc_eval oc_c30_1350)

lemma oc_c30_1351: "oc_sub oc_b30 1351"
  by (oc_eval oc_c30_1351)

lemma oc_c30_1352: "oc_sub oc_b30 1352"
  by (oc_eval oc_c30_1352)

lemma oc_c30_1353: "oc_sub oc_b30 1353"
  by (oc_eval oc_c30_1353)

lemma oc_c30_1354: "oc_sub oc_b30 1354"
  by (oc_eval oc_c30_1354)

lemma oc_c30_1355: "oc_sub oc_b30 1355"
  by (oc_eval oc_c30_1355)

lemma oc_c30_1356: "oc_sub oc_b30 1356"
  by (oc_eval oc_c30_1356)

lemma oc_c30_1357: "oc_sub oc_b30 1357"
  by (oc_eval oc_c30_1357)

lemma oc_c30_1358: "oc_sub oc_b30 1358"
  by (oc_eval oc_c30_1358)

lemma oc_c30_1359: "oc_sub oc_b30 1359"
  by (oc_eval oc_c30_1359)

lemma upt_c30_084: "[1344..<1360] = [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]"
  by (simp add: upt_rec)

lemma sec_c30_084: "\<forall>j\<in>{16 * 84..<16 * 84 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 84..<16 * 84 + 16}"
  then have "j \<in> set [1344..<1360]" unfolding set_upt by simp
  then have "j \<in> set [1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359]" unfolding upt_c30_084 .
  then show "oc_sub oc_b30 j" using oc_c30_1344 oc_c30_1345 oc_c30_1346 oc_c30_1347 oc_c30_1348 oc_c30_1349 oc_c30_1350 oc_c30_1351 oc_c30_1352 oc_c30_1353 oc_c30_1354 oc_c30_1355 oc_c30_1356 oc_c30_1357 oc_c30_1358 oc_c30_1359
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
