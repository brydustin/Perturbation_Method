theory OCX_nc_097
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1552: "oc_sub None 1552"
  by (oc_eval oc_nc_1552)

lemma oc_nc_1553: "oc_sub None 1553"
  by (oc_eval oc_nc_1553)

lemma oc_nc_1554: "oc_sub None 1554"
  by (oc_eval oc_nc_1554)

lemma oc_nc_1555: "oc_sub None 1555"
  by (oc_eval oc_nc_1555)

lemma oc_nc_1556: "oc_sub None 1556"
  by (oc_eval oc_nc_1556)

lemma oc_nc_1557: "oc_sub None 1557"
  by (oc_eval oc_nc_1557)

lemma oc_nc_1558: "oc_sub None 1558"
  by (oc_eval oc_nc_1558)

lemma oc_nc_1559: "oc_sub None 1559"
  by (oc_eval oc_nc_1559)

lemma oc_nc_1560: "oc_sub None 1560"
  by (oc_eval oc_nc_1560)

lemma oc_nc_1561: "oc_sub None 1561"
  by (oc_eval oc_nc_1561)

lemma oc_nc_1562: "oc_sub None 1562"
  by (oc_eval oc_nc_1562)

lemma oc_nc_1563: "oc_sub None 1563"
  by (oc_eval oc_nc_1563)

lemma oc_nc_1564: "oc_sub None 1564"
  by (oc_eval oc_nc_1564)

lemma oc_nc_1565: "oc_sub None 1565"
  by (oc_eval oc_nc_1565)

lemma oc_nc_1566: "oc_sub None 1566"
  by (oc_eval oc_nc_1566)

lemma oc_nc_1567: "oc_sub None 1567"
  by (oc_eval oc_nc_1567)

lemma upt_nc_097: "[1552..<1568] = [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]"
  by (simp add: upt_rec)

lemma sec_nc_097: "\<forall>j\<in>{16 * 97..<16 * 97 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 97..<16 * 97 + 16}"
  then have "j \<in> set [1552..<1568]" unfolding set_upt by simp
  then have "j \<in> set [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]" unfolding upt_nc_097 .
  then show "oc_sub None j" using oc_nc_1552 oc_nc_1553 oc_nc_1554 oc_nc_1555 oc_nc_1556 oc_nc_1557 oc_nc_1558 oc_nc_1559 oc_nc_1560 oc_nc_1561 oc_nc_1562 oc_nc_1563 oc_nc_1564 oc_nc_1565 oc_nc_1566 oc_nc_1567
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
