theory GDCX_nc_091
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1456: "gdc_sub None 1456"
  by (gdc_eval gdc_nc_1456)

lemma gdc_nc_1457: "gdc_sub None 1457"
  by (gdc_eval gdc_nc_1457)

lemma gdc_nc_1458: "gdc_sub None 1458"
  by (gdc_eval gdc_nc_1458)

lemma gdc_nc_1459: "gdc_sub None 1459"
  by (gdc_eval gdc_nc_1459)

lemma gdc_nc_1460: "gdc_sub None 1460"
  by (gdc_eval gdc_nc_1460)

lemma gdc_nc_1461: "gdc_sub None 1461"
  by (gdc_eval gdc_nc_1461)

lemma gdc_nc_1462: "gdc_sub None 1462"
  by (gdc_eval gdc_nc_1462)

lemma gdc_nc_1463: "gdc_sub None 1463"
  by (gdc_eval gdc_nc_1463)

lemma gdc_nc_1464: "gdc_sub None 1464"
  by (gdc_eval gdc_nc_1464)

lemma gdc_nc_1465: "gdc_sub None 1465"
  by (gdc_eval gdc_nc_1465)

lemma gdc_nc_1466: "gdc_sub None 1466"
  by (gdc_eval gdc_nc_1466)

lemma gdc_nc_1467: "gdc_sub None 1467"
  by (gdc_eval gdc_nc_1467)

lemma gdc_nc_1468: "gdc_sub None 1468"
  by (gdc_eval gdc_nc_1468)

lemma gdc_nc_1469: "gdc_sub None 1469"
  by (gdc_eval gdc_nc_1469)

lemma gdc_nc_1470: "gdc_sub None 1470"
  by (gdc_eval gdc_nc_1470)

lemma gdc_nc_1471: "gdc_sub None 1471"
  by (gdc_eval gdc_nc_1471)

lemma gupt_nc_091: "[1456..<1472] = [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]"
  by (simp add: upt_rec)

lemma gsec_nc_091: "\<forall>j\<in>{16 * 91..<16 * 91 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 91..<16 * 91 + 16}"
  then have "j \<in> set [1456..<1472]" unfolding set_upt by simp
  then have "j \<in> set [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]" unfolding gupt_nc_091 .
  then show "gdc_sub None j" using gdc_nc_1456 gdc_nc_1457 gdc_nc_1458 gdc_nc_1459 gdc_nc_1460 gdc_nc_1461 gdc_nc_1462 gdc_nc_1463 gdc_nc_1464 gdc_nc_1465 gdc_nc_1466 gdc_nc_1467 gdc_nc_1468 gdc_nc_1469 gdc_nc_1470 gdc_nc_1471
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
