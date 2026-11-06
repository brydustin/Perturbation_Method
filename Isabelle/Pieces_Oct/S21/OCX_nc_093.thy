theory OCX_nc_093
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1488: "oc_sub None 1488"
  by (oc_eval oc_nc_1488)

lemma oc_nc_1489: "oc_sub None 1489"
  by (oc_eval oc_nc_1489)

lemma oc_nc_1490: "oc_sub None 1490"
  by (oc_eval oc_nc_1490)

lemma oc_nc_1491: "oc_sub None 1491"
  by (oc_eval oc_nc_1491)

lemma oc_nc_1492: "oc_sub None 1492"
  by (oc_eval oc_nc_1492)

lemma oc_nc_1493: "oc_sub None 1493"
  by (oc_eval oc_nc_1493)

lemma oc_nc_1494: "oc_sub None 1494"
  by (oc_eval oc_nc_1494)

lemma oc_nc_1495: "oc_sub None 1495"
  by (oc_eval oc_nc_1495)

lemma oc_nc_1496: "oc_sub None 1496"
  by (oc_eval oc_nc_1496)

lemma oc_nc_1497: "oc_sub None 1497"
  by (oc_eval oc_nc_1497)

lemma oc_nc_1498: "oc_sub None 1498"
  by (oc_eval oc_nc_1498)

lemma oc_nc_1499: "oc_sub None 1499"
  by (oc_eval oc_nc_1499)

lemma oc_nc_1500: "oc_sub None 1500"
  by (oc_eval oc_nc_1500)

lemma oc_nc_1501: "oc_sub None 1501"
  by (oc_eval oc_nc_1501)

lemma oc_nc_1502: "oc_sub None 1502"
  by (oc_eval oc_nc_1502)

lemma oc_nc_1503: "oc_sub None 1503"
  by (oc_eval oc_nc_1503)

lemma upt_nc_093: "[1488..<1504] = [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]"
  by (simp add: upt_rec)

lemma sec_nc_093: "\<forall>j\<in>{16 * 93..<16 * 93 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 93..<16 * 93 + 16}"
  then have "j \<in> set [1488..<1504]" unfolding set_upt by simp
  then have "j \<in> set [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]" unfolding upt_nc_093 .
  then show "oc_sub None j" using oc_nc_1488 oc_nc_1489 oc_nc_1490 oc_nc_1491 oc_nc_1492 oc_nc_1493 oc_nc_1494 oc_nc_1495 oc_nc_1496 oc_nc_1497 oc_nc_1498 oc_nc_1499 oc_nc_1500 oc_nc_1501 oc_nc_1502 oc_nc_1503
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
