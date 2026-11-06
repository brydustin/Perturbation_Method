theory GDCX_nc_094
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1504: "gdc_sub None 1504"
  by (gdc_eval gdc_nc_1504)

lemma gdc_nc_1505: "gdc_sub None 1505"
  by (gdc_eval gdc_nc_1505)

lemma gdc_nc_1506: "gdc_sub None 1506"
  by (gdc_eval gdc_nc_1506)

lemma gdc_nc_1507: "gdc_sub None 1507"
  by (gdc_eval gdc_nc_1507)

lemma gdc_nc_1508: "gdc_sub None 1508"
  by (gdc_eval gdc_nc_1508)

lemma gdc_nc_1509: "gdc_sub None 1509"
  by (gdc_eval gdc_nc_1509)

lemma gdc_nc_1510: "gdc_sub None 1510"
  by (gdc_eval gdc_nc_1510)

lemma gdc_nc_1511: "gdc_sub None 1511"
  by (gdc_eval gdc_nc_1511)

lemma gdc_nc_1512: "gdc_sub None 1512"
  by (gdc_eval gdc_nc_1512)

lemma gdc_nc_1513: "gdc_sub None 1513"
  by (gdc_eval gdc_nc_1513)

lemma gdc_nc_1514: "gdc_sub None 1514"
  by (gdc_eval gdc_nc_1514)

lemma gdc_nc_1515: "gdc_sub None 1515"
  by (gdc_eval gdc_nc_1515)

lemma gdc_nc_1516: "gdc_sub None 1516"
  by (gdc_eval gdc_nc_1516)

lemma gdc_nc_1517: "gdc_sub None 1517"
  by (gdc_eval gdc_nc_1517)

lemma gdc_nc_1518: "gdc_sub None 1518"
  by (gdc_eval gdc_nc_1518)

lemma gdc_nc_1519: "gdc_sub None 1519"
  by (gdc_eval gdc_nc_1519)

lemma gupt_nc_094: "[1504..<1520] = [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]"
  by (simp add: upt_rec)

lemma gsec_nc_094: "\<forall>j\<in>{16 * 94..<16 * 94 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 94..<16 * 94 + 16}"
  then have "j \<in> set [1504..<1520]" unfolding set_upt by simp
  then have "j \<in> set [1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519]" unfolding gupt_nc_094 .
  then show "gdc_sub None j" using gdc_nc_1504 gdc_nc_1505 gdc_nc_1506 gdc_nc_1507 gdc_nc_1508 gdc_nc_1509 gdc_nc_1510 gdc_nc_1511 gdc_nc_1512 gdc_nc_1513 gdc_nc_1514 gdc_nc_1515 gdc_nc_1516 gdc_nc_1517 gdc_nc_1518 gdc_nc_1519
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
