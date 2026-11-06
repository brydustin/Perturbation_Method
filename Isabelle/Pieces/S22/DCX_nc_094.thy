theory DCX_nc_094
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1504: "dc_sub None 1504"
  by (dc_eval dc_nc_1504)

lemma dc_nc_1505: "dc_sub None 1505"
  by (dc_eval dc_nc_1505)

lemma dc_nc_1506: "dc_sub None 1506"
  by (dc_eval dc_nc_1506)

lemma dc_nc_1507: "dc_sub None 1507"
  by (dc_eval dc_nc_1507)

lemma dc_nc_1508: "dc_sub None 1508"
  by (dc_eval dc_nc_1508)

lemma dc_nc_1509: "dc_sub None 1509"
  by (dc_eval dc_nc_1509)

lemma dc_nc_1510: "dc_sub None 1510"
  by (dc_eval dc_nc_1510)

lemma dc_nc_1511: "dc_sub None 1511"
  by (dc_eval dc_nc_1511)

lemma dc_nc_1512: "dc_sub None 1512"
  by (dc_eval dc_nc_1512)

lemma dc_nc_1513: "dc_sub None 1513"
  by (dc_eval dc_nc_1513)

lemma dc_nc_1514: "dc_sub None 1514"
  by (dc_eval dc_nc_1514)

lemma dc_nc_1515: "dc_sub None 1515"
  by (dc_eval dc_nc_1515)

lemma dc_nc_1516: "dc_sub None 1516"
  by (dc_eval dc_nc_1516)

lemma dc_nc_1517: "dc_sub None 1517"
  by (dc_eval dc_nc_1517)

lemma dc_nc_1518: "dc_sub None 1518"
  by (dc_eval dc_nc_1518)

lemma dc_nc_1519: "dc_sub None 1519"
  by (dc_eval dc_nc_1519)

lemma upt_nc_094: "[1504..<1520] = [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]"
  by (simp add: upt_rec)

lemma sec_nc_094: "\<forall>j\<in>{16 * 94..<16 * 94 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 94..<16 * 94 + 16}"
  then have "j \<in> set [1504..<1520]" unfolding set_upt by simp
  then have "j \<in> set [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]" unfolding upt_nc_094 .
  then show "dc_sub None j" using dc_nc_1504 dc_nc_1505 dc_nc_1506 dc_nc_1507 dc_nc_1508 dc_nc_1509 dc_nc_1510 dc_nc_1511 dc_nc_1512 dc_nc_1513 dc_nc_1514 dc_nc_1515 dc_nc_1516 dc_nc_1517 dc_nc_1518 dc_nc_1519
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
