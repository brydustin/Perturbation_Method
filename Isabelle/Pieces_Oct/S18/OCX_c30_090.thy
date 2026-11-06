theory OCX_c30_090
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1440: "oc_sub oc_b30 1440"
  by (oc_eval oc_c30_1440)

lemma oc_c30_1441: "oc_sub oc_b30 1441"
  by (oc_eval oc_c30_1441)

lemma oc_c30_1442: "oc_sub oc_b30 1442"
  by (oc_eval oc_c30_1442)

lemma oc_c30_1443: "oc_sub oc_b30 1443"
  by (oc_eval oc_c30_1443)

lemma oc_c30_1444: "oc_sub oc_b30 1444"
  by (oc_eval oc_c30_1444)

lemma oc_c30_1445: "oc_sub oc_b30 1445"
  by (oc_eval oc_c30_1445)

lemma oc_c30_1446: "oc_sub oc_b30 1446"
  by (oc_eval oc_c30_1446)

lemma oc_c30_1447: "oc_sub oc_b30 1447"
  by (oc_eval oc_c30_1447)

lemma oc_c30_1448: "oc_sub oc_b30 1448"
  by (oc_eval oc_c30_1448)

lemma oc_c30_1449: "oc_sub oc_b30 1449"
  by (oc_eval oc_c30_1449)

lemma oc_c30_1450: "oc_sub oc_b30 1450"
  by (oc_eval oc_c30_1450)

lemma oc_c30_1451: "oc_sub oc_b30 1451"
  by (oc_eval oc_c30_1451)

lemma oc_c30_1452: "oc_sub oc_b30 1452"
  by (oc_eval oc_c30_1452)

lemma oc_c30_1453: "oc_sub oc_b30 1453"
  by (oc_eval oc_c30_1453)

lemma oc_c30_1454: "oc_sub oc_b30 1454"
  by (oc_eval oc_c30_1454)

lemma oc_c30_1455: "oc_sub oc_b30 1455"
  by (oc_eval oc_c30_1455)

lemma upt_c30_090: "[1440..<1456] = [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]"
  by (simp add: upt_rec)

lemma sec_c30_090: "\<forall>j\<in>{16 * 90..<16 * 90 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 90..<16 * 90 + 16}"
  then have "j \<in> set [1440..<1456]" unfolding set_upt by simp
  then have "j \<in> set [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]" unfolding upt_c30_090 .
  then show "oc_sub oc_b30 j" using oc_c30_1440 oc_c30_1441 oc_c30_1442 oc_c30_1443 oc_c30_1444 oc_c30_1445 oc_c30_1446 oc_c30_1447 oc_c30_1448 oc_c30_1449 oc_c30_1450 oc_c30_1451 oc_c30_1452 oc_c30_1453 oc_c30_1454 oc_c30_1455
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
