theory OCX_nc_086
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1376: "oc_sub None 1376"
  by (oc_eval oc_nc_1376)

lemma oc_nc_1377: "oc_sub None 1377"
  by (oc_eval oc_nc_1377)

lemma oc_nc_1378: "oc_sub None 1378"
  by (oc_eval oc_nc_1378)

lemma oc_nc_1379: "oc_sub None 1379"
  by (oc_eval oc_nc_1379)

lemma oc_nc_1380: "oc_sub None 1380"
  by (oc_eval oc_nc_1380)

lemma oc_nc_1381: "oc_sub None 1381"
  by (oc_eval oc_nc_1381)

lemma oc_nc_1382: "oc_sub None 1382"
  by (oc_eval oc_nc_1382)

lemma oc_nc_1383: "oc_sub None 1383"
  by (oc_eval oc_nc_1383)

lemma oc_nc_1384: "oc_sub None 1384"
  by (oc_eval oc_nc_1384)

lemma oc_nc_1385: "oc_sub None 1385"
  by (oc_eval oc_nc_1385)

lemma oc_nc_1386: "oc_sub None 1386"
  by (oc_eval oc_nc_1386)

lemma oc_nc_1387: "oc_sub None 1387"
  by (oc_eval oc_nc_1387)

lemma oc_nc_1388: "oc_sub None 1388"
  by (oc_eval oc_nc_1388)

lemma oc_nc_1389: "oc_sub None 1389"
  by (oc_eval oc_nc_1389)

lemma oc_nc_1390: "oc_sub None 1390"
  by (oc_eval oc_nc_1390)

lemma oc_nc_1391: "oc_sub None 1391"
  by (oc_eval oc_nc_1391)

lemma upt_nc_086: "[1376..<1392] = [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]"
  by (simp add: upt_rec)

lemma sec_nc_086: "\<forall>j\<in>{16 * 86..<16 * 86 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 86..<16 * 86 + 16}"
  then have "j \<in> set [1376..<1392]" unfolding set_upt by simp
  then have "j \<in> set [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]" unfolding upt_nc_086 .
  then show "oc_sub None j" using oc_nc_1376 oc_nc_1377 oc_nc_1378 oc_nc_1379 oc_nc_1380 oc_nc_1381 oc_nc_1382 oc_nc_1383 oc_nc_1384 oc_nc_1385 oc_nc_1386 oc_nc_1387 oc_nc_1388 oc_nc_1389 oc_nc_1390 oc_nc_1391
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
