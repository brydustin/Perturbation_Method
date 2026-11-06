theory GOCX_nc_097
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1552: "goc_sub None 1552"
  by (goc_eval goc_nc_1552)

lemma goc_nc_1553: "goc_sub None 1553"
  by (goc_eval goc_nc_1553)

lemma goc_nc_1554: "goc_sub None 1554"
  by (goc_eval goc_nc_1554)

lemma goc_nc_1555: "goc_sub None 1555"
  by (goc_eval goc_nc_1555)

lemma goc_nc_1556: "goc_sub None 1556"
  by (goc_eval goc_nc_1556)

lemma goc_nc_1557: "goc_sub None 1557"
  by (goc_eval goc_nc_1557)

lemma goc_nc_1558: "goc_sub None 1558"
  by (goc_eval goc_nc_1558)

lemma goc_nc_1559: "goc_sub None 1559"
  by (goc_eval goc_nc_1559)

lemma goc_nc_1560: "goc_sub None 1560"
  by (goc_eval goc_nc_1560)

lemma goc_nc_1561: "goc_sub None 1561"
  by (goc_eval goc_nc_1561)

lemma goc_nc_1562: "goc_sub None 1562"
  by (goc_eval goc_nc_1562)

lemma goc_nc_1563: "goc_sub None 1563"
  by (goc_eval goc_nc_1563)

lemma goc_nc_1564: "goc_sub None 1564"
  by (goc_eval goc_nc_1564)

lemma goc_nc_1565: "goc_sub None 1565"
  by (goc_eval goc_nc_1565)

lemma goc_nc_1566: "goc_sub None 1566"
  by (goc_eval goc_nc_1566)

lemma goc_nc_1567: "goc_sub None 1567"
  by (goc_eval goc_nc_1567)

lemma gupt_nc_097: "[1552..<1568] = [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]"
  by (simp add: upt_rec)

lemma gsec_nc_097: "\<forall>j\<in>{16 * 97..<16 * 97 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 97..<16 * 97 + 16}"
  then have "j \<in> set [1552..<1568]" unfolding set_upt by simp
  then have "j \<in> set [1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567]" unfolding gupt_nc_097 .
  then show "goc_sub None j" using goc_nc_1552 goc_nc_1553 goc_nc_1554 goc_nc_1555 goc_nc_1556 goc_nc_1557 goc_nc_1558 goc_nc_1559 goc_nc_1560 goc_nc_1561 goc_nc_1562 goc_nc_1563 goc_nc_1564 goc_nc_1565 goc_nc_1566 goc_nc_1567
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
