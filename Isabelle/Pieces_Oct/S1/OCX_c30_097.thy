theory OCX_c30_097
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1552: "oc_sub oc_b30 1552"
  by (oc_eval oc_c30_1552)

lemma oc_c30_1553: "oc_sub oc_b30 1553"
  by (oc_eval oc_c30_1553)

lemma oc_c30_1554: "oc_sub oc_b30 1554"
  by (oc_eval oc_c30_1554)

lemma oc_c30_1555: "oc_sub oc_b30 1555"
  by (oc_eval oc_c30_1555)

lemma oc_c30_1556: "oc_sub oc_b30 1556"
  by (oc_eval oc_c30_1556)

lemma oc_c30_1557: "oc_sub oc_b30 1557"
  by (oc_eval oc_c30_1557)

lemma oc_c30_1558: "oc_sub oc_b30 1558"
  by (oc_eval oc_c30_1558)

lemma oc_c30_1559: "oc_sub oc_b30 1559"
  by (oc_eval oc_c30_1559)

lemma oc_c30_1560: "oc_sub oc_b30 1560"
  by (oc_eval oc_c30_1560)

lemma oc_c30_1561: "oc_sub oc_b30 1561"
  by (oc_eval oc_c30_1561)

lemma oc_c30_1562: "oc_sub oc_b30 1562"
  by (oc_eval oc_c30_1562)

lemma oc_c30_1563: "oc_sub oc_b30 1563"
  by (oc_eval oc_c30_1563)

lemma oc_c30_1564: "oc_sub oc_b30 1564"
  by (oc_eval oc_c30_1564)

lemma oc_c30_1565: "oc_sub oc_b30 1565"
  by (oc_eval oc_c30_1565)

lemma oc_c30_1566: "oc_sub oc_b30 1566"
  by (oc_eval oc_c30_1566)

lemma oc_c30_1567: "oc_sub oc_b30 1567"
  by (oc_eval oc_c30_1567)

lemma upt_c30_097: "[1552..<1568] = [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]"
  by (simp add: upt_rec)

lemma sec_c30_097: "\<forall>j\<in>{16 * 97..<16 * 97 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 97..<16 * 97 + 16}"
  then have "j \<in> set [1552..<1568]" unfolding set_upt by simp
  then have "j \<in> set [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]" unfolding upt_c30_097 .
  then show "oc_sub oc_b30 j" using oc_c30_1552 oc_c30_1553 oc_c30_1554 oc_c30_1555 oc_c30_1556 oc_c30_1557 oc_c30_1558 oc_c30_1559 oc_c30_1560 oc_c30_1561 oc_c30_1562 oc_c30_1563 oc_c30_1564 oc_c30_1565 oc_c30_1566 oc_c30_1567
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
