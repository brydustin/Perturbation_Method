theory OCX_nc_096
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1536: "oc_sub None 1536"
  by (oc_eval oc_nc_1536)

lemma oc_nc_1537: "oc_sub None 1537"
  by (oc_eval oc_nc_1537)

lemma oc_nc_1538: "oc_sub None 1538"
  by (oc_eval oc_nc_1538)

lemma oc_nc_1539: "oc_sub None 1539"
  by (oc_eval oc_nc_1539)

lemma oc_nc_1540: "oc_sub None 1540"
  by (oc_eval oc_nc_1540)

lemma oc_nc_1541: "oc_sub None 1541"
  by (oc_eval oc_nc_1541)

lemma oc_nc_1542: "oc_sub None 1542"
  by (oc_eval oc_nc_1542)

lemma oc_nc_1543: "oc_sub None 1543"
  by (oc_eval oc_nc_1543)

lemma oc_nc_1544: "oc_sub None 1544"
  by (oc_eval oc_nc_1544)

lemma oc_nc_1545: "oc_sub None 1545"
  by (oc_eval oc_nc_1545)

lemma oc_nc_1546: "oc_sub None 1546"
  by (oc_eval oc_nc_1546)

lemma oc_nc_1547: "oc_sub None 1547"
  by (oc_eval oc_nc_1547)

lemma oc_nc_1548: "oc_sub None 1548"
  by (oc_eval oc_nc_1548)

lemma oc_nc_1549: "oc_sub None 1549"
  by (oc_eval oc_nc_1549)

lemma oc_nc_1550: "oc_sub None 1550"
  by (oc_eval oc_nc_1550)

lemma oc_nc_1551: "oc_sub None 1551"
  by (oc_eval oc_nc_1551)

lemma upt_nc_096: "[1536..<1552] = [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]"
  by (simp add: upt_rec)

lemma sec_nc_096: "\<forall>j\<in>{16 * 96..<16 * 96 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 96..<16 * 96 + 16}"
  then have "j \<in> set [1536..<1552]" unfolding set_upt by simp
  then have "j \<in> set [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]" unfolding upt_nc_096 .
  then show "oc_sub None j" using oc_nc_1536 oc_nc_1537 oc_nc_1538 oc_nc_1539 oc_nc_1540 oc_nc_1541 oc_nc_1542 oc_nc_1543 oc_nc_1544 oc_nc_1545 oc_nc_1546 oc_nc_1547 oc_nc_1548 oc_nc_1549 oc_nc_1550 oc_nc_1551
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
