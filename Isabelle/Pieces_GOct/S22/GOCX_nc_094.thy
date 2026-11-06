theory GOCX_nc_094
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1504: "goc_sub None 1504"
  by (goc_eval goc_nc_1504)

lemma goc_nc_1505: "goc_sub None 1505"
  by (goc_eval goc_nc_1505)

lemma goc_nc_1506: "goc_sub None 1506"
  by (goc_eval goc_nc_1506)

lemma goc_nc_1507: "goc_sub None 1507"
  by (goc_eval goc_nc_1507)

lemma goc_nc_1508: "goc_sub None 1508"
  by (goc_eval goc_nc_1508)

lemma goc_nc_1509: "goc_sub None 1509"
  by (goc_eval goc_nc_1509)

lemma goc_nc_1510: "goc_sub None 1510"
  by (goc_eval goc_nc_1510)

lemma goc_nc_1511: "goc_sub None 1511"
  by (goc_eval goc_nc_1511)

lemma goc_nc_1512: "goc_sub None 1512"
  by (goc_eval goc_nc_1512)

lemma goc_nc_1513: "goc_sub None 1513"
  by (goc_eval goc_nc_1513)

lemma goc_nc_1514: "goc_sub None 1514"
  by (goc_eval goc_nc_1514)

lemma goc_nc_1515: "goc_sub None 1515"
  by (goc_eval goc_nc_1515)

lemma goc_nc_1516: "goc_sub None 1516"
  by (goc_eval goc_nc_1516)

lemma goc_nc_1517: "goc_sub None 1517"
  by (goc_eval goc_nc_1517)

lemma goc_nc_1518: "goc_sub None 1518"
  by (goc_eval goc_nc_1518)

lemma goc_nc_1519: "goc_sub None 1519"
  by (goc_eval goc_nc_1519)

lemma gupt_nc_094: "[1504..<1520] = [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]"
  by (simp add: upt_rec)

lemma gsec_nc_094: "\<forall>j\<in>{16 * 94..<16 * 94 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 94..<16 * 94 + 16}"
  then have "j \<in> set [1504..<1520]" unfolding set_upt by simp
  then have "j \<in> set [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]" unfolding gupt_nc_094 .
  then show "goc_sub None j" using goc_nc_1504 goc_nc_1505 goc_nc_1506 goc_nc_1507 goc_nc_1508 goc_nc_1509 goc_nc_1510 goc_nc_1511 goc_nc_1512 goc_nc_1513 goc_nc_1514 goc_nc_1515 goc_nc_1516 goc_nc_1517 goc_nc_1518 goc_nc_1519
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
