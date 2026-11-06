theory OCX_c30_096
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1536: "oc_sub oc_b30 1536"
  by (oc_eval oc_c30_1536)

lemma oc_c30_1537: "oc_sub oc_b30 1537"
  by (oc_eval oc_c30_1537)

lemma oc_c30_1538: "oc_sub oc_b30 1538"
  by (oc_eval oc_c30_1538)

lemma oc_c30_1539: "oc_sub oc_b30 1539"
  by (oc_eval oc_c30_1539)

lemma oc_c30_1540: "oc_sub oc_b30 1540"
  by (oc_eval oc_c30_1540)

lemma oc_c30_1541: "oc_sub oc_b30 1541"
  by (oc_eval oc_c30_1541)

lemma oc_c30_1542: "oc_sub oc_b30 1542"
  by (oc_eval oc_c30_1542)

lemma oc_c30_1543: "oc_sub oc_b30 1543"
  by (oc_eval oc_c30_1543)

lemma oc_c30_1544: "oc_sub oc_b30 1544"
  by (oc_eval oc_c30_1544)

lemma oc_c30_1545: "oc_sub oc_b30 1545"
  by (oc_eval oc_c30_1545)

lemma oc_c30_1546: "oc_sub oc_b30 1546"
  by (oc_eval oc_c30_1546)

lemma oc_c30_1547: "oc_sub oc_b30 1547"
  by (oc_eval oc_c30_1547)

lemma oc_c30_1548: "oc_sub oc_b30 1548"
  by (oc_eval oc_c30_1548)

lemma oc_c30_1549: "oc_sub oc_b30 1549"
  by (oc_eval oc_c30_1549)

lemma oc_c30_1550: "oc_sub oc_b30 1550"
  by (oc_eval oc_c30_1550)

lemma oc_c30_1551: "oc_sub oc_b30 1551"
  by (oc_eval oc_c30_1551)

lemma upt_c30_096: "[1536..<1552] = [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]"
  by (simp add: upt_rec)

lemma sec_c30_096: "\<forall>j\<in>{16 * 96..<16 * 96 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 96..<16 * 96 + 16}"
  then have "j \<in> set [1536..<1552]" unfolding set_upt by simp
  then have "j \<in> set [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]" unfolding upt_c30_096 .
  then show "oc_sub oc_b30 j" using oc_c30_1536 oc_c30_1537 oc_c30_1538 oc_c30_1539 oc_c30_1540 oc_c30_1541 oc_c30_1542 oc_c30_1543 oc_c30_1544 oc_c30_1545 oc_c30_1546 oc_c30_1547 oc_c30_1548 oc_c30_1549 oc_c30_1550 oc_c30_1551
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
