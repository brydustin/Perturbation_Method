theory DCX_nc_097
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1552: "dc_sub None 1552"
  by (dc_eval dc_nc_1552)

lemma dc_nc_1553: "dc_sub None 1553"
  by (dc_eval dc_nc_1553)

lemma dc_nc_1554: "dc_sub None 1554"
  by (dc_eval dc_nc_1554)

lemma dc_nc_1555: "dc_sub None 1555"
  by (dc_eval dc_nc_1555)

lemma dc_nc_1556: "dc_sub None 1556"
  by (dc_eval dc_nc_1556)

lemma dc_nc_1557: "dc_sub None 1557"
  by (dc_eval dc_nc_1557)

lemma dc_nc_1558: "dc_sub None 1558"
  by (dc_eval dc_nc_1558)

lemma dc_nc_1559: "dc_sub None 1559"
  by (dc_eval dc_nc_1559)

lemma dc_nc_1560: "dc_sub None 1560"
  by (dc_eval dc_nc_1560)

lemma dc_nc_1561: "dc_sub None 1561"
  by (dc_eval dc_nc_1561)

lemma dc_nc_1562: "dc_sub None 1562"
  by (dc_eval dc_nc_1562)

lemma dc_nc_1563: "dc_sub None 1563"
  by (dc_eval dc_nc_1563)

lemma dc_nc_1564: "dc_sub None 1564"
  by (dc_eval dc_nc_1564)

lemma dc_nc_1565: "dc_sub None 1565"
  by (dc_eval dc_nc_1565)

lemma dc_nc_1566: "dc_sub None 1566"
  by (dc_eval dc_nc_1566)

lemma dc_nc_1567: "dc_sub None 1567"
  by (dc_eval dc_nc_1567)

lemma upt_nc_097: "[1552..<1568] = [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]"
  by (simp add: upt_rec)

lemma sec_nc_097: "\<forall>j\<in>{16 * 97..<16 * 97 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 97..<16 * 97 + 16}"
  then have "j \<in> set [1552..<1568]" unfolding set_upt by simp
  then have "j \<in> set [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]" unfolding upt_nc_097 .
  then show "dc_sub None j" using dc_nc_1552 dc_nc_1553 dc_nc_1554 dc_nc_1555 dc_nc_1556 dc_nc_1557 dc_nc_1558 dc_nc_1559 dc_nc_1560 dc_nc_1561 dc_nc_1562 dc_nc_1563 dc_nc_1564 dc_nc_1565 dc_nc_1566 dc_nc_1567
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
