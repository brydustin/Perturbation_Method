theory GOCX_nc_096
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1536: "goc_sub None 1536"
  by (goc_eval goc_nc_1536)

lemma goc_nc_1537: "goc_sub None 1537"
  by (goc_eval goc_nc_1537)

lemma goc_nc_1538: "goc_sub None 1538"
  by (goc_eval goc_nc_1538)

lemma goc_nc_1539: "goc_sub None 1539"
  by (goc_eval goc_nc_1539)

lemma goc_nc_1540: "goc_sub None 1540"
  by (goc_eval goc_nc_1540)

lemma goc_nc_1541: "goc_sub None 1541"
  by (goc_eval goc_nc_1541)

lemma goc_nc_1542: "goc_sub None 1542"
  by (goc_eval goc_nc_1542)

lemma goc_nc_1543: "goc_sub None 1543"
  by (goc_eval goc_nc_1543)

lemma goc_nc_1544: "goc_sub None 1544"
  by (goc_eval goc_nc_1544)

lemma goc_nc_1545: "goc_sub None 1545"
  by (goc_eval goc_nc_1545)

lemma goc_nc_1546: "goc_sub None 1546"
  by (goc_eval goc_nc_1546)

lemma goc_nc_1547: "goc_sub None 1547"
  by (goc_eval goc_nc_1547)

lemma goc_nc_1548: "goc_sub None 1548"
  by (goc_eval goc_nc_1548)

lemma goc_nc_1549: "goc_sub None 1549"
  by (goc_eval goc_nc_1549)

lemma goc_nc_1550: "goc_sub None 1550"
  by (goc_eval goc_nc_1550)

lemma goc_nc_1551: "goc_sub None 1551"
  by (goc_eval goc_nc_1551)

lemma gupt_nc_096: "[1536..<1552] = [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]"
  by (simp add: upt_rec)

lemma gsec_nc_096: "\<forall>j\<in>{16 * 96..<16 * 96 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 96..<16 * 96 + 16}"
  then have "j \<in> set [1536..<1552]" unfolding set_upt by simp
  then have "j \<in> set [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]" unfolding gupt_nc_096 .
  then show "goc_sub None j" using goc_nc_1536 goc_nc_1537 goc_nc_1538 goc_nc_1539 goc_nc_1540 goc_nc_1541 goc_nc_1542 goc_nc_1543 goc_nc_1544 goc_nc_1545 goc_nc_1546 goc_nc_1547 goc_nc_1548 goc_nc_1549 goc_nc_1550 goc_nc_1551
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
