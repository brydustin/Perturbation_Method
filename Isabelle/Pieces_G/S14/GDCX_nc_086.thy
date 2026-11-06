theory GDCX_nc_086
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1376: "gdc_sub None 1376"
  by (gdc_eval gdc_nc_1376)

lemma gdc_nc_1377: "gdc_sub None 1377"
  by (gdc_eval gdc_nc_1377)

lemma gdc_nc_1378: "gdc_sub None 1378"
  by (gdc_eval gdc_nc_1378)

lemma gdc_nc_1379: "gdc_sub None 1379"
  by (gdc_eval gdc_nc_1379)

lemma gdc_nc_1380: "gdc_sub None 1380"
  by (gdc_eval gdc_nc_1380)

lemma gdc_nc_1381: "gdc_sub None 1381"
  by (gdc_eval gdc_nc_1381)

lemma gdc_nc_1382: "gdc_sub None 1382"
  by (gdc_eval gdc_nc_1382)

lemma gdc_nc_1383: "gdc_sub None 1383"
  by (gdc_eval gdc_nc_1383)

lemma gdc_nc_1384: "gdc_sub None 1384"
  by (gdc_eval gdc_nc_1384)

lemma gdc_nc_1385: "gdc_sub None 1385"
  by (gdc_eval gdc_nc_1385)

lemma gdc_nc_1386: "gdc_sub None 1386"
  by (gdc_eval gdc_nc_1386)

lemma gdc_nc_1387: "gdc_sub None 1387"
  by (gdc_eval gdc_nc_1387)

lemma gdc_nc_1388: "gdc_sub None 1388"
  by (gdc_eval gdc_nc_1388)

lemma gdc_nc_1389: "gdc_sub None 1389"
  by (gdc_eval gdc_nc_1389)

lemma gdc_nc_1390: "gdc_sub None 1390"
  by (gdc_eval gdc_nc_1390)

lemma gdc_nc_1391: "gdc_sub None 1391"
  by (gdc_eval gdc_nc_1391)

lemma gupt_nc_086: "[1376..<1392] = [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]"
  by (simp add: upt_rec)

lemma gsec_nc_086: "\<forall>j\<in>{16 * 86..<16 * 86 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 86..<16 * 86 + 16}"
  then have "j \<in> set [1376..<1392]" unfolding set_upt by simp
  then have "j \<in> set [1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391]" unfolding gupt_nc_086 .
  then show "gdc_sub None j" using gdc_nc_1376 gdc_nc_1377 gdc_nc_1378 gdc_nc_1379 gdc_nc_1380 gdc_nc_1381 gdc_nc_1382 gdc_nc_1383 gdc_nc_1384 gdc_nc_1385 gdc_nc_1386 gdc_nc_1387 gdc_nc_1388 gdc_nc_1389 gdc_nc_1390 gdc_nc_1391
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
