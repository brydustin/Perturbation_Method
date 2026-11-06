theory OCX_nc_091
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1456: "oc_sub None 1456"
  by (oc_eval oc_nc_1456)

lemma oc_nc_1457: "oc_sub None 1457"
  by (oc_eval oc_nc_1457)

lemma oc_nc_1458: "oc_sub None 1458"
  by (oc_eval oc_nc_1458)

lemma oc_nc_1459: "oc_sub None 1459"
  by (oc_eval oc_nc_1459)

lemma oc_nc_1460: "oc_sub None 1460"
  by (oc_eval oc_nc_1460)

lemma oc_nc_1461: "oc_sub None 1461"
  by (oc_eval oc_nc_1461)

lemma oc_nc_1462: "oc_sub None 1462"
  by (oc_eval oc_nc_1462)

lemma oc_nc_1463: "oc_sub None 1463"
  by (oc_eval oc_nc_1463)

lemma oc_nc_1464: "oc_sub None 1464"
  by (oc_eval oc_nc_1464)

lemma oc_nc_1465: "oc_sub None 1465"
  by (oc_eval oc_nc_1465)

lemma oc_nc_1466: "oc_sub None 1466"
  by (oc_eval oc_nc_1466)

lemma oc_nc_1467: "oc_sub None 1467"
  by (oc_eval oc_nc_1467)

lemma oc_nc_1468: "oc_sub None 1468"
  by (oc_eval oc_nc_1468)

lemma oc_nc_1469: "oc_sub None 1469"
  by (oc_eval oc_nc_1469)

lemma oc_nc_1470: "oc_sub None 1470"
  by (oc_eval oc_nc_1470)

lemma oc_nc_1471: "oc_sub None 1471"
  by (oc_eval oc_nc_1471)

lemma upt_nc_091: "[1456..<1472] = [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]"
  by (simp add: upt_rec)

lemma sec_nc_091: "\<forall>j\<in>{16 * 91..<16 * 91 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 91..<16 * 91 + 16}"
  then have "j \<in> set [1456..<1472]" unfolding set_upt by simp
  then have "j \<in> set [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]" unfolding upt_nc_091 .
  then show "oc_sub None j" using oc_nc_1456 oc_nc_1457 oc_nc_1458 oc_nc_1459 oc_nc_1460 oc_nc_1461 oc_nc_1462 oc_nc_1463 oc_nc_1464 oc_nc_1465 oc_nc_1466 oc_nc_1467 oc_nc_1468 oc_nc_1469 oc_nc_1470 oc_nc_1471
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
