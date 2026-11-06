theory DCX_c30_096
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1536: "dc_sub dc_b30 1536"
  by (dc_eval dc_c30_1536)

lemma dc_c30_1537: "dc_sub dc_b30 1537"
  by (dc_eval dc_c30_1537)

lemma dc_c30_1538: "dc_sub dc_b30 1538"
  by (dc_eval dc_c30_1538)

lemma dc_c30_1539: "dc_sub dc_b30 1539"
  by (dc_eval dc_c30_1539)

lemma dc_c30_1540: "dc_sub dc_b30 1540"
  by (dc_eval dc_c30_1540)

lemma dc_c30_1541: "dc_sub dc_b30 1541"
  by (dc_eval dc_c30_1541)

lemma dc_c30_1542: "dc_sub dc_b30 1542"
  by (dc_eval dc_c30_1542)

lemma dc_c30_1543: "dc_sub dc_b30 1543"
  by (dc_eval dc_c30_1543)

lemma dc_c30_1544: "dc_sub dc_b30 1544"
  by (dc_eval dc_c30_1544)

lemma dc_c30_1545: "dc_sub dc_b30 1545"
  by (dc_eval dc_c30_1545)

lemma dc_c30_1546: "dc_sub dc_b30 1546"
  by (dc_eval dc_c30_1546)

lemma dc_c30_1547: "dc_sub dc_b30 1547"
  by (dc_eval dc_c30_1547)

lemma dc_c30_1548: "dc_sub dc_b30 1548"
  by (dc_eval dc_c30_1548)

lemma dc_c30_1549: "dc_sub dc_b30 1549"
  by (dc_eval dc_c30_1549)

lemma dc_c30_1550: "dc_sub dc_b30 1550"
  by (dc_eval dc_c30_1550)

lemma dc_c30_1551: "dc_sub dc_b30 1551"
  by (dc_eval dc_c30_1551)

lemma upt_c30_096: "[1536..<1552] = [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]"
  by (simp add: upt_rec)

lemma sec_c30_096: "\<forall>j\<in>{16 * 96..<16 * 96 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 96..<16 * 96 + 16}"
  then have "j \<in> set [1536..<1552]" unfolding set_upt by simp
  then have "j \<in> set [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]" unfolding upt_c30_096 .
  then show "dc_sub dc_b30 j" using dc_c30_1536 dc_c30_1537 dc_c30_1538 dc_c30_1539 dc_c30_1540 dc_c30_1541 dc_c30_1542 dc_c30_1543 dc_c30_1544 dc_c30_1545 dc_c30_1546 dc_c30_1547 dc_c30_1548 dc_c30_1549 dc_c30_1550 dc_c30_1551
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
