theory OCX_c30_094
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1504: "oc_sub oc_b30 1504"
  by (oc_eval oc_c30_1504)

lemma oc_c30_1505: "oc_sub oc_b30 1505"
  by (oc_eval oc_c30_1505)

lemma oc_c30_1506: "oc_sub oc_b30 1506"
  by (oc_eval oc_c30_1506)

lemma oc_c30_1507: "oc_sub oc_b30 1507"
  by (oc_eval oc_c30_1507)

lemma oc_c30_1508: "oc_sub oc_b30 1508"
  by (oc_eval oc_c30_1508)

lemma oc_c30_1509: "oc_sub oc_b30 1509"
  by (oc_eval oc_c30_1509)

lemma oc_c30_1510: "oc_sub oc_b30 1510"
  by (oc_eval oc_c30_1510)

lemma oc_c30_1511: "oc_sub oc_b30 1511"
  by (oc_eval oc_c30_1511)

lemma oc_c30_1512: "oc_sub oc_b30 1512"
  by (oc_eval oc_c30_1512)

lemma oc_c30_1513: "oc_sub oc_b30 1513"
  by (oc_eval oc_c30_1513)

lemma oc_c30_1514: "oc_sub oc_b30 1514"
  by (oc_eval oc_c30_1514)

lemma oc_c30_1515: "oc_sub oc_b30 1515"
  by (oc_eval oc_c30_1515)

lemma oc_c30_1516: "oc_sub oc_b30 1516"
  by (oc_eval oc_c30_1516)

lemma oc_c30_1517: "oc_sub oc_b30 1517"
  by (oc_eval oc_c30_1517)

lemma oc_c30_1518: "oc_sub oc_b30 1518"
  by (oc_eval oc_c30_1518)

lemma oc_c30_1519: "oc_sub oc_b30 1519"
  by (oc_eval oc_c30_1519)

lemma upt_c30_094: "[1504..<1520] = [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]"
  by (simp add: upt_rec)

lemma sec_c30_094: "\<forall>j\<in>{16 * 94..<16 * 94 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 94..<16 * 94 + 16}"
  then have "j \<in> set [1504..<1520]" unfolding set_upt by simp
  then have "j \<in> set [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]" unfolding upt_c30_094 .
  then show "oc_sub oc_b30 j" using oc_c30_1504 oc_c30_1505 oc_c30_1506 oc_c30_1507 oc_c30_1508 oc_c30_1509 oc_c30_1510 oc_c30_1511 oc_c30_1512 oc_c30_1513 oc_c30_1514 oc_c30_1515 oc_c30_1516 oc_c30_1517 oc_c30_1518 oc_c30_1519
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
