theory GOCX_nc_093
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1488: "goc_sub None 1488"
  by (goc_eval goc_nc_1488)

lemma goc_nc_1489: "goc_sub None 1489"
  by (goc_eval goc_nc_1489)

lemma goc_nc_1490: "goc_sub None 1490"
  by (goc_eval goc_nc_1490)

lemma goc_nc_1491: "goc_sub None 1491"
  by (goc_eval goc_nc_1491)

lemma goc_nc_1492: "goc_sub None 1492"
  by (goc_eval goc_nc_1492)

lemma goc_nc_1493: "goc_sub None 1493"
  by (goc_eval goc_nc_1493)

lemma goc_nc_1494: "goc_sub None 1494"
  by (goc_eval goc_nc_1494)

lemma goc_nc_1495: "goc_sub None 1495"
  by (goc_eval goc_nc_1495)

lemma goc_nc_1496: "goc_sub None 1496"
  by (goc_eval goc_nc_1496)

lemma goc_nc_1497: "goc_sub None 1497"
  by (goc_eval goc_nc_1497)

lemma goc_nc_1498: "goc_sub None 1498"
  by (goc_eval goc_nc_1498)

lemma goc_nc_1499: "goc_sub None 1499"
  by (goc_eval goc_nc_1499)

lemma goc_nc_1500: "goc_sub None 1500"
  by (goc_eval goc_nc_1500)

lemma goc_nc_1501: "goc_sub None 1501"
  by (goc_eval goc_nc_1501)

lemma goc_nc_1502: "goc_sub None 1502"
  by (goc_eval goc_nc_1502)

lemma goc_nc_1503: "goc_sub None 1503"
  by (goc_eval goc_nc_1503)

lemma gupt_nc_093: "[1488..<1504] = [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]"
  by (simp add: upt_rec)

lemma gsec_nc_093: "\<forall>j\<in>{16 * 93..<16 * 93 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 93..<16 * 93 + 16}"
  then have "j \<in> set [1488..<1504]" unfolding set_upt by simp
  then have "j \<in> set [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]" unfolding gupt_nc_093 .
  then show "goc_sub None j" using goc_nc_1488 goc_nc_1489 goc_nc_1490 goc_nc_1491 goc_nc_1492 goc_nc_1493 goc_nc_1494 goc_nc_1495 goc_nc_1496 goc_nc_1497 goc_nc_1498 goc_nc_1499 goc_nc_1500 goc_nc_1501 goc_nc_1502 goc_nc_1503
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
