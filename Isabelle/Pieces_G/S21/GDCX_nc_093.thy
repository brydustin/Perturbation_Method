theory GDCX_nc_093
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1488: "gdc_sub None 1488"
  by (gdc_eval gdc_nc_1488)

lemma gdc_nc_1489: "gdc_sub None 1489"
  by (gdc_eval gdc_nc_1489)

lemma gdc_nc_1490: "gdc_sub None 1490"
  by (gdc_eval gdc_nc_1490)

lemma gdc_nc_1491: "gdc_sub None 1491"
  by (gdc_eval gdc_nc_1491)

lemma gdc_nc_1492: "gdc_sub None 1492"
  by (gdc_eval gdc_nc_1492)

lemma gdc_nc_1493: "gdc_sub None 1493"
  by (gdc_eval gdc_nc_1493)

lemma gdc_nc_1494: "gdc_sub None 1494"
  by (gdc_eval gdc_nc_1494)

lemma gdc_nc_1495: "gdc_sub None 1495"
  by (gdc_eval gdc_nc_1495)

lemma gdc_nc_1496: "gdc_sub None 1496"
  by (gdc_eval gdc_nc_1496)

lemma gdc_nc_1497: "gdc_sub None 1497"
  by (gdc_eval gdc_nc_1497)

lemma gdc_nc_1498: "gdc_sub None 1498"
  by (gdc_eval gdc_nc_1498)

lemma gdc_nc_1499: "gdc_sub None 1499"
  by (gdc_eval gdc_nc_1499)

lemma gdc_nc_1500: "gdc_sub None 1500"
  by (gdc_eval gdc_nc_1500)

lemma gdc_nc_1501: "gdc_sub None 1501"
  by (gdc_eval gdc_nc_1501)

lemma gdc_nc_1502: "gdc_sub None 1502"
  by (gdc_eval gdc_nc_1502)

lemma gdc_nc_1503: "gdc_sub None 1503"
  by (gdc_eval gdc_nc_1503)

lemma gupt_nc_093: "[1488..<1504] = [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]"
  by (simp add: upt_rec)

lemma gsec_nc_093: "\<forall>j\<in>{16 * 93..<16 * 93 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 93..<16 * 93 + 16}"
  then have "j \<in> set [1488..<1504]" unfolding set_upt by simp
  then have "j \<in> set [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]" unfolding gupt_nc_093 .
  then show "gdc_sub None j" using gdc_nc_1488 gdc_nc_1489 gdc_nc_1490 gdc_nc_1491 gdc_nc_1492 gdc_nc_1493 gdc_nc_1494 gdc_nc_1495 gdc_nc_1496 gdc_nc_1497 gdc_nc_1498 gdc_nc_1499 gdc_nc_1500 gdc_nc_1501 gdc_nc_1502 gdc_nc_1503
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
