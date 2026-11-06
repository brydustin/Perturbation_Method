theory GDCX_nc_097
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1552: "gdc_sub None 1552"
  by (gdc_eval gdc_nc_1552)

lemma gdc_nc_1553: "gdc_sub None 1553"
  by (gdc_eval gdc_nc_1553)

lemma gdc_nc_1554: "gdc_sub None 1554"
  by (gdc_eval gdc_nc_1554)

lemma gdc_nc_1555: "gdc_sub None 1555"
  by (gdc_eval gdc_nc_1555)

lemma gdc_nc_1556: "gdc_sub None 1556"
  by (gdc_eval gdc_nc_1556)

lemma gdc_nc_1557: "gdc_sub None 1557"
  by (gdc_eval gdc_nc_1557)

lemma gdc_nc_1558: "gdc_sub None 1558"
  by (gdc_eval gdc_nc_1558)

lemma gdc_nc_1559: "gdc_sub None 1559"
  by (gdc_eval gdc_nc_1559)

lemma gdc_nc_1560: "gdc_sub None 1560"
  by (gdc_eval gdc_nc_1560)

lemma gdc_nc_1561: "gdc_sub None 1561"
  by (gdc_eval gdc_nc_1561)

lemma gdc_nc_1562: "gdc_sub None 1562"
  by (gdc_eval gdc_nc_1562)

lemma gdc_nc_1563: "gdc_sub None 1563"
  by (gdc_eval gdc_nc_1563)

lemma gdc_nc_1564: "gdc_sub None 1564"
  by (gdc_eval gdc_nc_1564)

lemma gdc_nc_1565: "gdc_sub None 1565"
  by (gdc_eval gdc_nc_1565)

lemma gdc_nc_1566: "gdc_sub None 1566"
  by (gdc_eval gdc_nc_1566)

lemma gdc_nc_1567: "gdc_sub None 1567"
  by (gdc_eval gdc_nc_1567)

lemma gupt_nc_097: "[1552..<1568] = [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]"
  by (simp add: upt_rec)

lemma gsec_nc_097: "\<forall>j\<in>{16 * 97..<16 * 97 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 97..<16 * 97 + 16}"
  then have "j \<in> set [1552..<1568]" unfolding set_upt by simp
  then have "j \<in> set [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]" unfolding gupt_nc_097 .
  then show "gdc_sub None j" using gdc_nc_1552 gdc_nc_1553 gdc_nc_1554 gdc_nc_1555 gdc_nc_1556 gdc_nc_1557 gdc_nc_1558 gdc_nc_1559 gdc_nc_1560 gdc_nc_1561 gdc_nc_1562 gdc_nc_1563 gdc_nc_1564 gdc_nc_1565 gdc_nc_1566 gdc_nc_1567
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
