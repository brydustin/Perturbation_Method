theory OCX_c30_093
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1488: "oc_sub oc_b30 1488"
  by (oc_eval oc_c30_1488)

lemma oc_c30_1489: "oc_sub oc_b30 1489"
  by (oc_eval oc_c30_1489)

lemma oc_c30_1490: "oc_sub oc_b30 1490"
  by (oc_eval oc_c30_1490)

lemma oc_c30_1491: "oc_sub oc_b30 1491"
  by (oc_eval oc_c30_1491)

lemma oc_c30_1492: "oc_sub oc_b30 1492"
  by (oc_eval oc_c30_1492)

lemma oc_c30_1493: "oc_sub oc_b30 1493"
  by (oc_eval oc_c30_1493)

lemma oc_c30_1494: "oc_sub oc_b30 1494"
  by (oc_eval oc_c30_1494)

lemma oc_c30_1495: "oc_sub oc_b30 1495"
  by (oc_eval oc_c30_1495)

lemma oc_c30_1496: "oc_sub oc_b30 1496"
  by (oc_eval oc_c30_1496)

lemma oc_c30_1497: "oc_sub oc_b30 1497"
  by (oc_eval oc_c30_1497)

lemma oc_c30_1498: "oc_sub oc_b30 1498"
  by (oc_eval oc_c30_1498)

lemma oc_c30_1499: "oc_sub oc_b30 1499"
  by (oc_eval oc_c30_1499)

lemma oc_c30_1500: "oc_sub oc_b30 1500"
  by (oc_eval oc_c30_1500)

lemma oc_c30_1501: "oc_sub oc_b30 1501"
  by (oc_eval oc_c30_1501)

lemma oc_c30_1502: "oc_sub oc_b30 1502"
  by (oc_eval oc_c30_1502)

lemma oc_c30_1503: "oc_sub oc_b30 1503"
  by (oc_eval oc_c30_1503)

lemma upt_c30_093: "[1488..<1504] = [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]"
  by (simp add: upt_rec)

lemma sec_c30_093: "\<forall>j\<in>{16 * 93..<16 * 93 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 93..<16 * 93 + 16}"
  then have "j \<in> set [1488..<1504]" unfolding set_upt by simp
  then have "j \<in> set [1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503]" unfolding upt_c30_093 .
  then show "oc_sub oc_b30 j" using oc_c30_1488 oc_c30_1489 oc_c30_1490 oc_c30_1491 oc_c30_1492 oc_c30_1493 oc_c30_1494 oc_c30_1495 oc_c30_1496 oc_c30_1497 oc_c30_1498 oc_c30_1499 oc_c30_1500 oc_c30_1501 oc_c30_1502 oc_c30_1503
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
