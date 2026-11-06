theory GDCX_nc_096
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1536: "gdc_sub None 1536"
  by (gdc_eval gdc_nc_1536)

lemma gdc_nc_1537: "gdc_sub None 1537"
  by (gdc_eval gdc_nc_1537)

lemma gdc_nc_1538: "gdc_sub None 1538"
  by (gdc_eval gdc_nc_1538)

lemma gdc_nc_1539: "gdc_sub None 1539"
  by (gdc_eval gdc_nc_1539)

lemma gdc_nc_1540: "gdc_sub None 1540"
  by (gdc_eval gdc_nc_1540)

lemma gdc_nc_1541: "gdc_sub None 1541"
  by (gdc_eval gdc_nc_1541)

lemma gdc_nc_1542: "gdc_sub None 1542"
  by (gdc_eval gdc_nc_1542)

lemma gdc_nc_1543: "gdc_sub None 1543"
  by (gdc_eval gdc_nc_1543)

lemma gdc_nc_1544: "gdc_sub None 1544"
  by (gdc_eval gdc_nc_1544)

lemma gdc_nc_1545: "gdc_sub None 1545"
  by (gdc_eval gdc_nc_1545)

lemma gdc_nc_1546: "gdc_sub None 1546"
  by (gdc_eval gdc_nc_1546)

lemma gdc_nc_1547: "gdc_sub None 1547"
  by (gdc_eval gdc_nc_1547)

lemma gdc_nc_1548: "gdc_sub None 1548"
  by (gdc_eval gdc_nc_1548)

lemma gdc_nc_1549: "gdc_sub None 1549"
  by (gdc_eval gdc_nc_1549)

lemma gdc_nc_1550: "gdc_sub None 1550"
  by (gdc_eval gdc_nc_1550)

lemma gdc_nc_1551: "gdc_sub None 1551"
  by (gdc_eval gdc_nc_1551)

lemma gupt_nc_096: "[1536..<1552] = [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]"
  by (simp add: upt_rec)

lemma gsec_nc_096: "\<forall>j\<in>{16 * 96..<16 * 96 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 96..<16 * 96 + 16}"
  then have "j \<in> set [1536..<1552]" unfolding set_upt by simp
  then have "j \<in> set [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]" unfolding gupt_nc_096 .
  then show "gdc_sub None j" using gdc_nc_1536 gdc_nc_1537 gdc_nc_1538 gdc_nc_1539 gdc_nc_1540 gdc_nc_1541 gdc_nc_1542 gdc_nc_1543 gdc_nc_1544 gdc_nc_1545 gdc_nc_1546 gdc_nc_1547 gdc_nc_1548 gdc_nc_1549 gdc_nc_1550 gdc_nc_1551
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
