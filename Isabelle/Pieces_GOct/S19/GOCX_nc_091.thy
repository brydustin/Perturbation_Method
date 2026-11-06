theory GOCX_nc_091
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1456: "goc_sub None 1456"
  by (goc_eval goc_nc_1456)

lemma goc_nc_1457: "goc_sub None 1457"
  by (goc_eval goc_nc_1457)

lemma goc_nc_1458: "goc_sub None 1458"
  by (goc_eval goc_nc_1458)

lemma goc_nc_1459: "goc_sub None 1459"
  by (goc_eval goc_nc_1459)

lemma goc_nc_1460: "goc_sub None 1460"
  by (goc_eval goc_nc_1460)

lemma goc_nc_1461: "goc_sub None 1461"
  by (goc_eval goc_nc_1461)

lemma goc_nc_1462: "goc_sub None 1462"
  by (goc_eval goc_nc_1462)

lemma goc_nc_1463: "goc_sub None 1463"
  by (goc_eval goc_nc_1463)

lemma goc_nc_1464: "goc_sub None 1464"
  by (goc_eval goc_nc_1464)

lemma goc_nc_1465: "goc_sub None 1465"
  by (goc_eval goc_nc_1465)

lemma goc_nc_1466: "goc_sub None 1466"
  by (goc_eval goc_nc_1466)

lemma goc_nc_1467: "goc_sub None 1467"
  by (goc_eval goc_nc_1467)

lemma goc_nc_1468: "goc_sub None 1468"
  by (goc_eval goc_nc_1468)

lemma goc_nc_1469: "goc_sub None 1469"
  by (goc_eval goc_nc_1469)

lemma goc_nc_1470: "goc_sub None 1470"
  by (goc_eval goc_nc_1470)

lemma goc_nc_1471: "goc_sub None 1471"
  by (goc_eval goc_nc_1471)

lemma gupt_nc_091: "[1456..<1472] = [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]"
  by (simp add: upt_rec)

lemma gsec_nc_091: "\<forall>j\<in>{16 * 91..<16 * 91 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 91..<16 * 91 + 16}"
  then have "j \<in> set [1456..<1472]" unfolding set_upt by simp
  then have "j \<in> set [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]" unfolding gupt_nc_091 .
  then show "goc_sub None j" using goc_nc_1456 goc_nc_1457 goc_nc_1458 goc_nc_1459 goc_nc_1460 goc_nc_1461 goc_nc_1462 goc_nc_1463 goc_nc_1464 goc_nc_1465 goc_nc_1466 goc_nc_1467 goc_nc_1468 goc_nc_1469 goc_nc_1470 goc_nc_1471
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
