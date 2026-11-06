theory OCX_nc_094
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1504: "oc_sub None 1504"
  by (oc_eval oc_nc_1504)

lemma oc_nc_1505: "oc_sub None 1505"
  by (oc_eval oc_nc_1505)

lemma oc_nc_1506: "oc_sub None 1506"
  by (oc_eval oc_nc_1506)

lemma oc_nc_1507: "oc_sub None 1507"
  by (oc_eval oc_nc_1507)

lemma oc_nc_1508: "oc_sub None 1508"
  by (oc_eval oc_nc_1508)

lemma oc_nc_1509: "oc_sub None 1509"
  by (oc_eval oc_nc_1509)

lemma oc_nc_1510: "oc_sub None 1510"
  by (oc_eval oc_nc_1510)

lemma oc_nc_1511: "oc_sub None 1511"
  by (oc_eval oc_nc_1511)

lemma oc_nc_1512: "oc_sub None 1512"
  by (oc_eval oc_nc_1512)

lemma oc_nc_1513: "oc_sub None 1513"
  by (oc_eval oc_nc_1513)

lemma oc_nc_1514: "oc_sub None 1514"
  by (oc_eval oc_nc_1514)

lemma oc_nc_1515: "oc_sub None 1515"
  by (oc_eval oc_nc_1515)

lemma oc_nc_1516: "oc_sub None 1516"
  by (oc_eval oc_nc_1516)

lemma oc_nc_1517: "oc_sub None 1517"
  by (oc_eval oc_nc_1517)

lemma oc_nc_1518: "oc_sub None 1518"
  by (oc_eval oc_nc_1518)

lemma oc_nc_1519: "oc_sub None 1519"
  by (oc_eval oc_nc_1519)

lemma upt_nc_094: "[1504..<1520] = [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]"
  by (simp add: upt_rec)

lemma sec_nc_094: "\<forall>j\<in>{16 * 94..<16 * 94 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 94..<16 * 94 + 16}"
  then have "j \<in> set [1504..<1520]" unfolding set_upt by simp
  then have "j \<in> set [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]" unfolding upt_nc_094 .
  then show "oc_sub None j" using oc_nc_1504 oc_nc_1505 oc_nc_1506 oc_nc_1507 oc_nc_1508 oc_nc_1509 oc_nc_1510 oc_nc_1511 oc_nc_1512 oc_nc_1513 oc_nc_1514 oc_nc_1515 oc_nc_1516 oc_nc_1517 oc_nc_1518 oc_nc_1519
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
