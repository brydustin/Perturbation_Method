theory OCX_c30_086
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1376: "oc_sub oc_b30 1376"
  by (oc_eval oc_c30_1376)

lemma oc_c30_1377: "oc_sub oc_b30 1377"
  by (oc_eval oc_c30_1377)

lemma oc_c30_1378: "oc_sub oc_b30 1378"
  by (oc_eval oc_c30_1378)

lemma oc_c30_1379: "oc_sub oc_b30 1379"
  by (oc_eval oc_c30_1379)

lemma oc_c30_1380: "oc_sub oc_b30 1380"
  by (oc_eval oc_c30_1380)

lemma oc_c30_1381: "oc_sub oc_b30 1381"
  by (oc_eval oc_c30_1381)

lemma oc_c30_1382: "oc_sub oc_b30 1382"
  by (oc_eval oc_c30_1382)

lemma oc_c30_1383: "oc_sub oc_b30 1383"
  by (oc_eval oc_c30_1383)

lemma oc_c30_1384: "oc_sub oc_b30 1384"
  by (oc_eval oc_c30_1384)

lemma oc_c30_1385: "oc_sub oc_b30 1385"
  by (oc_eval oc_c30_1385)

lemma oc_c30_1386: "oc_sub oc_b30 1386"
  by (oc_eval oc_c30_1386)

lemma oc_c30_1387: "oc_sub oc_b30 1387"
  by (oc_eval oc_c30_1387)

lemma oc_c30_1388: "oc_sub oc_b30 1388"
  by (oc_eval oc_c30_1388)

lemma oc_c30_1389: "oc_sub oc_b30 1389"
  by (oc_eval oc_c30_1389)

lemma oc_c30_1390: "oc_sub oc_b30 1390"
  by (oc_eval oc_c30_1390)

lemma oc_c30_1391: "oc_sub oc_b30 1391"
  by (oc_eval oc_c30_1391)

lemma upt_c30_086: "[1376..<1392] = [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]"
  by (simp add: upt_rec)

lemma sec_c30_086: "\<forall>j\<in>{16 * 86..<16 * 86 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 86..<16 * 86 + 16}"
  then have "j \<in> set [1376..<1392]" unfolding set_upt by simp
  then have "j \<in> set [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]" unfolding upt_c30_086 .
  then show "oc_sub oc_b30 j" using oc_c30_1376 oc_c30_1377 oc_c30_1378 oc_c30_1379 oc_c30_1380 oc_c30_1381 oc_c30_1382 oc_c30_1383 oc_c30_1384 oc_c30_1385 oc_c30_1386 oc_c30_1387 oc_c30_1388 oc_c30_1389 oc_c30_1390 oc_c30_1391
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
