theory DCX_c30_090
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1440: "dc_sub dc_b30 1440"
  by (dc_eval dc_c30_1440)

lemma dc_c30_1441: "dc_sub dc_b30 1441"
  by (dc_eval dc_c30_1441)

lemma dc_c30_1442: "dc_sub dc_b30 1442"
  by (dc_eval dc_c30_1442)

lemma dc_c30_1443: "dc_sub dc_b30 1443"
  by (dc_eval dc_c30_1443)

lemma dc_c30_1444: "dc_sub dc_b30 1444"
  by (dc_eval dc_c30_1444)

lemma dc_c30_1445: "dc_sub dc_b30 1445"
  by (dc_eval dc_c30_1445)

lemma dc_c30_1446: "dc_sub dc_b30 1446"
  by (dc_eval dc_c30_1446)

lemma dc_c30_1447: "dc_sub dc_b30 1447"
  by (dc_eval dc_c30_1447)

lemma dc_c30_1448: "dc_sub dc_b30 1448"
  by (dc_eval dc_c30_1448)

lemma dc_c30_1449: "dc_sub dc_b30 1449"
  by (dc_eval dc_c30_1449)

lemma dc_c30_1450: "dc_sub dc_b30 1450"
  by (dc_eval dc_c30_1450)

lemma dc_c30_1451: "dc_sub dc_b30 1451"
  by (dc_eval dc_c30_1451)

lemma dc_c30_1452: "dc_sub dc_b30 1452"
  by (dc_eval dc_c30_1452)

lemma dc_c30_1453: "dc_sub dc_b30 1453"
  by (dc_eval dc_c30_1453)

lemma dc_c30_1454: "dc_sub dc_b30 1454"
  by (dc_eval dc_c30_1454)

lemma dc_c30_1455: "dc_sub dc_b30 1455"
  by (dc_eval dc_c30_1455)

lemma upt_c30_090: "[1440..<1456] = [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]"
  by (simp add: upt_rec)

lemma sec_c30_090: "\<forall>j\<in>{16 * 90..<16 * 90 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 90..<16 * 90 + 16}"
  then have "j \<in> set [1440..<1456]" unfolding set_upt by simp
  then have "j \<in> set [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]" unfolding upt_c30_090 .
  then show "dc_sub dc_b30 j" using dc_c30_1440 dc_c30_1441 dc_c30_1442 dc_c30_1443 dc_c30_1444 dc_c30_1445 dc_c30_1446 dc_c30_1447 dc_c30_1448 dc_c30_1449 dc_c30_1450 dc_c30_1451 dc_c30_1452 dc_c30_1453 dc_c30_1454 dc_c30_1455
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
