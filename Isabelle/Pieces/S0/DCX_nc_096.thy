theory DCX_nc_096
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1536: "dc_sub None 1536"
  by (dc_eval dc_nc_1536)

lemma dc_nc_1537: "dc_sub None 1537"
  by (dc_eval dc_nc_1537)

lemma dc_nc_1538: "dc_sub None 1538"
  by (dc_eval dc_nc_1538)

lemma dc_nc_1539: "dc_sub None 1539"
  by (dc_eval dc_nc_1539)

lemma dc_nc_1540: "dc_sub None 1540"
  by (dc_eval dc_nc_1540)

lemma dc_nc_1541: "dc_sub None 1541"
  by (dc_eval dc_nc_1541)

lemma dc_nc_1542: "dc_sub None 1542"
  by (dc_eval dc_nc_1542)

lemma dc_nc_1543: "dc_sub None 1543"
  by (dc_eval dc_nc_1543)

lemma dc_nc_1544: "dc_sub None 1544"
  by (dc_eval dc_nc_1544)

lemma dc_nc_1545: "dc_sub None 1545"
  by (dc_eval dc_nc_1545)

lemma dc_nc_1546: "dc_sub None 1546"
  by (dc_eval dc_nc_1546)

lemma dc_nc_1547: "dc_sub None 1547"
  by (dc_eval dc_nc_1547)

lemma dc_nc_1548: "dc_sub None 1548"
  by (dc_eval dc_nc_1548)

lemma dc_nc_1549: "dc_sub None 1549"
  by (dc_eval dc_nc_1549)

lemma dc_nc_1550: "dc_sub None 1550"
  by (dc_eval dc_nc_1550)

lemma dc_nc_1551: "dc_sub None 1551"
  by (dc_eval dc_nc_1551)

lemma upt_nc_096: "[1536..<1552] = [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]"
  by (simp add: upt_rec)

lemma sec_nc_096: "\<forall>j\<in>{16 * 96..<16 * 96 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 96..<16 * 96 + 16}"
  then have "j \<in> set [1536..<1552]" unfolding set_upt by simp
  then have "j \<in> set [1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551]" unfolding upt_nc_096 .
  then show "dc_sub None j" using dc_nc_1536 dc_nc_1537 dc_nc_1538 dc_nc_1539 dc_nc_1540 dc_nc_1541 dc_nc_1542 dc_nc_1543 dc_nc_1544 dc_nc_1545 dc_nc_1546 dc_nc_1547 dc_nc_1548 dc_nc_1549 dc_nc_1550 dc_nc_1551
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
