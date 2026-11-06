theory DCX_c30_086
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1376: "dc_sub dc_b30 1376"
  by (dc_eval dc_c30_1376)

lemma dc_c30_1377: "dc_sub dc_b30 1377"
  by (dc_eval dc_c30_1377)

lemma dc_c30_1378: "dc_sub dc_b30 1378"
  by (dc_eval dc_c30_1378)

lemma dc_c30_1379: "dc_sub dc_b30 1379"
  by (dc_eval dc_c30_1379)

lemma dc_c30_1380: "dc_sub dc_b30 1380"
  by (dc_eval dc_c30_1380)

lemma dc_c30_1381: "dc_sub dc_b30 1381"
  by (dc_eval dc_c30_1381)

lemma dc_c30_1382: "dc_sub dc_b30 1382"
  by (dc_eval dc_c30_1382)

lemma dc_c30_1383: "dc_sub dc_b30 1383"
  by (dc_eval dc_c30_1383)

lemma dc_c30_1384: "dc_sub dc_b30 1384"
  by (dc_eval dc_c30_1384)

lemma dc_c30_1385: "dc_sub dc_b30 1385"
  by (dc_eval dc_c30_1385)

lemma dc_c30_1386: "dc_sub dc_b30 1386"
  by (dc_eval dc_c30_1386)

lemma dc_c30_1387: "dc_sub dc_b30 1387"
  by (dc_eval dc_c30_1387)

lemma dc_c30_1388: "dc_sub dc_b30 1388"
  by (dc_eval dc_c30_1388)

lemma dc_c30_1389: "dc_sub dc_b30 1389"
  by (dc_eval dc_c30_1389)

lemma dc_c30_1390: "dc_sub dc_b30 1390"
  by (dc_eval dc_c30_1390)

lemma dc_c30_1391: "dc_sub dc_b30 1391"
  by (dc_eval dc_c30_1391)

lemma upt_c30_086: "[1376..<1392] = [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]"
  by (simp add: upt_rec)

lemma sec_c30_086: "\<forall>j\<in>{16 * 86..<16 * 86 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 86..<16 * 86 + 16}"
  then have "j \<in> set [1376..<1392]" unfolding set_upt by simp
  then have "j \<in> set [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]" unfolding upt_c30_086 .
  then show "dc_sub dc_b30 j" using dc_c30_1376 dc_c30_1377 dc_c30_1378 dc_c30_1379 dc_c30_1380 dc_c30_1381 dc_c30_1382 dc_c30_1383 dc_c30_1384 dc_c30_1385 dc_c30_1386 dc_c30_1387 dc_c30_1388 dc_c30_1389 dc_c30_1390 dc_c30_1391
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
