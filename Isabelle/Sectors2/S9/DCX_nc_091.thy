theory DCX_nc_091
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1456: "dc_sub None 1456"
  by (dc_eval dc_nc_1456)

lemma dc_nc_1457: "dc_sub None 1457"
  by (dc_eval dc_nc_1457)

lemma dc_nc_1458: "dc_sub None 1458"
  by (dc_eval dc_nc_1458)

lemma dc_nc_1459: "dc_sub None 1459"
  by (dc_eval dc_nc_1459)

lemma dc_nc_1460: "dc_sub None 1460"
  by (dc_eval dc_nc_1460)

lemma dc_nc_1461: "dc_sub None 1461"
  by (dc_eval dc_nc_1461)

lemma dc_nc_1462: "dc_sub None 1462"
  by (dc_eval dc_nc_1462)

lemma dc_nc_1463: "dc_sub None 1463"
  by (dc_eval dc_nc_1463)

lemma dc_nc_1464: "dc_sub None 1464"
  by (dc_eval dc_nc_1464)

lemma dc_nc_1465: "dc_sub None 1465"
  by (dc_eval dc_nc_1465)

lemma dc_nc_1466: "dc_sub None 1466"
  by (dc_eval dc_nc_1466)

lemma dc_nc_1467: "dc_sub None 1467"
  by (dc_eval dc_nc_1467)

lemma dc_nc_1468: "dc_sub None 1468"
  by (dc_eval dc_nc_1468)

lemma dc_nc_1469: "dc_sub None 1469"
  by (dc_eval dc_nc_1469)

lemma dc_nc_1470: "dc_sub None 1470"
  by (dc_eval dc_nc_1470)

lemma dc_nc_1471: "dc_sub None 1471"
  by (dc_eval dc_nc_1471)

lemma upt_nc_091: "[1456..<1472] = [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]"
  by (simp add: upt_rec)

lemma sec_nc_091: "\<forall>j\<in>{16 * 91..<16 * 91 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 91..<16 * 91 + 16}"
  then have "j \<in> set [1456..<1472]" unfolding set_upt by simp
  then have "j \<in> set [1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471]" unfolding upt_nc_091 .
  then show "dc_sub None j" using dc_nc_1456 dc_nc_1457 dc_nc_1458 dc_nc_1459 dc_nc_1460 dc_nc_1461 dc_nc_1462 dc_nc_1463 dc_nc_1464 dc_nc_1465 dc_nc_1466 dc_nc_1467 dc_nc_1468 dc_nc_1469 dc_nc_1470 dc_nc_1471
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
