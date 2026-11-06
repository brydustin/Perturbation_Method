theory DCX_c30_097
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1552: "dc_sub dc_b30 1552"
  by (dc_eval dc_c30_1552)

lemma dc_c30_1553: "dc_sub dc_b30 1553"
  by (dc_eval dc_c30_1553)

lemma dc_c30_1554: "dc_sub dc_b30 1554"
  by (dc_eval dc_c30_1554)

lemma dc_c30_1555: "dc_sub dc_b30 1555"
  by (dc_eval dc_c30_1555)

lemma dc_c30_1556: "dc_sub dc_b30 1556"
  by (dc_eval dc_c30_1556)

lemma dc_c30_1557: "dc_sub dc_b30 1557"
  by (dc_eval dc_c30_1557)

lemma dc_c30_1558: "dc_sub dc_b30 1558"
  by (dc_eval dc_c30_1558)

lemma dc_c30_1559: "dc_sub dc_b30 1559"
  by (dc_eval dc_c30_1559)

lemma dc_c30_1560: "dc_sub dc_b30 1560"
  by (dc_eval dc_c30_1560)

lemma dc_c30_1561: "dc_sub dc_b30 1561"
  by (dc_eval dc_c30_1561)

lemma dc_c30_1562: "dc_sub dc_b30 1562"
  by (dc_eval dc_c30_1562)

lemma dc_c30_1563: "dc_sub dc_b30 1563"
  by (dc_eval dc_c30_1563)

lemma dc_c30_1564: "dc_sub dc_b30 1564"
  by (dc_eval dc_c30_1564)

lemma dc_c30_1565: "dc_sub dc_b30 1565"
  by (dc_eval dc_c30_1565)

lemma dc_c30_1566: "dc_sub dc_b30 1566"
  by (dc_eval dc_c30_1566)

lemma dc_c30_1567: "dc_sub dc_b30 1567"
  by (dc_eval dc_c30_1567)

lemma upt_c30_097: "[1552..<1568] = [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]"
  by (simp add: upt_rec)

lemma sec_c30_097: "\<forall>j\<in>{16 * 97..<16 * 97 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 97..<16 * 97 + 16}"
  then have "j \<in> set [1552..<1568]" unfolding set_upt by simp
  then have "j \<in> set [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]" unfolding upt_c30_097 .
  then show "dc_sub dc_b30 j" using dc_c30_1552 dc_c30_1553 dc_c30_1554 dc_c30_1555 dc_c30_1556 dc_c30_1557 dc_c30_1558 dc_c30_1559 dc_c30_1560 dc_c30_1561 dc_c30_1562 dc_c30_1563 dc_c30_1564 dc_c30_1565 dc_c30_1566 dc_c30_1567
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
