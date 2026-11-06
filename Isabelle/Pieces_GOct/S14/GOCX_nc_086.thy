theory GOCX_nc_086
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1376: "goc_sub None 1376"
  by (goc_eval goc_nc_1376)

lemma goc_nc_1377: "goc_sub None 1377"
  by (goc_eval goc_nc_1377)

lemma goc_nc_1378: "goc_sub None 1378"
  by (goc_eval goc_nc_1378)

lemma goc_nc_1379: "goc_sub None 1379"
  by (goc_eval goc_nc_1379)

lemma goc_nc_1380: "goc_sub None 1380"
  by (goc_eval goc_nc_1380)

lemma goc_nc_1381: "goc_sub None 1381"
  by (goc_eval goc_nc_1381)

lemma goc_nc_1382: "goc_sub None 1382"
  by (goc_eval goc_nc_1382)

lemma goc_nc_1383: "goc_sub None 1383"
  by (goc_eval goc_nc_1383)

lemma goc_nc_1384: "goc_sub None 1384"
  by (goc_eval goc_nc_1384)

lemma goc_nc_1385: "goc_sub None 1385"
  by (goc_eval goc_nc_1385)

lemma goc_nc_1386: "goc_sub None 1386"
  by (goc_eval goc_nc_1386)

lemma goc_nc_1387: "goc_sub None 1387"
  by (goc_eval goc_nc_1387)

lemma goc_nc_1388: "goc_sub None 1388"
  by (goc_eval goc_nc_1388)

lemma goc_nc_1389: "goc_sub None 1389"
  by (goc_eval goc_nc_1389)

lemma goc_nc_1390: "goc_sub None 1390"
  by (goc_eval goc_nc_1390)

lemma goc_nc_1391: "goc_sub None 1391"
  by (goc_eval goc_nc_1391)

lemma gupt_nc_086: "[1376..<1392] = [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]"
  by (simp add: upt_rec)

lemma gsec_nc_086: "\<forall>j\<in>{16 * 86..<16 * 86 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 86..<16 * 86 + 16}"
  then have "j \<in> set [1376..<1392]" unfolding set_upt by simp
  then have "j \<in> set [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]" unfolding gupt_nc_086 .
  then show "goc_sub None j" using goc_nc_1376 goc_nc_1377 goc_nc_1378 goc_nc_1379 goc_nc_1380 goc_nc_1381 goc_nc_1382 goc_nc_1383 goc_nc_1384 goc_nc_1385 goc_nc_1386 goc_nc_1387 goc_nc_1388 goc_nc_1389 goc_nc_1390 goc_nc_1391
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
