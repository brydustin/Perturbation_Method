theory DCX_c30_094
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1504: "dc_sub dc_b30 1504"
  by (dc_eval dc_c30_1504)

lemma dc_c30_1505: "dc_sub dc_b30 1505"
  by (dc_eval dc_c30_1505)

lemma dc_c30_1506: "dc_sub dc_b30 1506"
  by (dc_eval dc_c30_1506)

lemma dc_c30_1507: "dc_sub dc_b30 1507"
  by (dc_eval dc_c30_1507)

lemma dc_c30_1508: "dc_sub dc_b30 1508"
  by (dc_eval dc_c30_1508)

lemma dc_c30_1509: "dc_sub dc_b30 1509"
  by (dc_eval dc_c30_1509)

lemma dc_c30_1510: "dc_sub dc_b30 1510"
  by (dc_eval dc_c30_1510)

lemma dc_c30_1511: "dc_sub dc_b30 1511"
  by (dc_eval dc_c30_1511)

lemma dc_c30_1512: "dc_sub dc_b30 1512"
  by (dc_eval dc_c30_1512)

lemma dc_c30_1513: "dc_sub dc_b30 1513"
  by (dc_eval dc_c30_1513)

lemma dc_c30_1514: "dc_sub dc_b30 1514"
  by (dc_eval dc_c30_1514)

lemma dc_c30_1515: "dc_sub dc_b30 1515"
  by (dc_eval dc_c30_1515)

lemma dc_c30_1516: "dc_sub dc_b30 1516"
  by (dc_eval dc_c30_1516)

lemma dc_c30_1517: "dc_sub dc_b30 1517"
  by (dc_eval dc_c30_1517)

lemma dc_c30_1518: "dc_sub dc_b30 1518"
  by (dc_eval dc_c30_1518)

lemma dc_c30_1519: "dc_sub dc_b30 1519"
  by (dc_eval dc_c30_1519)

lemma upt_c30_094: "[1504..<1520] = [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]"
  by (simp add: upt_rec)

lemma sec_c30_094: "\<forall>j\<in>{16 * 94..<16 * 94 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 94..<16 * 94 + 16}"
  then have "j \<in> set [1504..<1520]" unfolding set_upt by simp
  then have "j \<in> set [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]" unfolding upt_c30_094 .
  then show "dc_sub dc_b30 j" using dc_c30_1504 dc_c30_1505 dc_c30_1506 dc_c30_1507 dc_c30_1508 dc_c30_1509 dc_c30_1510 dc_c30_1511 dc_c30_1512 dc_c30_1513 dc_c30_1514 dc_c30_1515 dc_c30_1516 dc_c30_1517 dc_c30_1518 dc_c30_1519
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
