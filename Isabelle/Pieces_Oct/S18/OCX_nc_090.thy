theory OCX_nc_090
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1440: "oc_sub None 1440"
  by (oc_eval oc_nc_1440)

lemma oc_nc_1441: "oc_sub None 1441"
  by (oc_eval oc_nc_1441)

lemma oc_nc_1442: "oc_sub None 1442"
  by (oc_eval oc_nc_1442)

lemma oc_nc_1443: "oc_sub None 1443"
  by (oc_eval oc_nc_1443)

lemma oc_nc_1444: "oc_sub None 1444"
  by (oc_eval oc_nc_1444)

lemma oc_nc_1445: "oc_sub None 1445"
  by (oc_eval oc_nc_1445)

lemma oc_nc_1446: "oc_sub None 1446"
  by (oc_eval oc_nc_1446)

lemma oc_nc_1447: "oc_sub None 1447"
  by (oc_eval oc_nc_1447)

lemma oc_nc_1448: "oc_sub None 1448"
  by (oc_eval oc_nc_1448)

lemma oc_nc_1449: "oc_sub None 1449"
  by (oc_eval oc_nc_1449)

lemma oc_nc_1450: "oc_sub None 1450"
  by (oc_eval oc_nc_1450)

lemma oc_nc_1451: "oc_sub None 1451"
  by (oc_eval oc_nc_1451)

lemma oc_nc_1452: "oc_sub None 1452"
  by (oc_eval oc_nc_1452)

lemma oc_nc_1453: "oc_sub None 1453"
  by (oc_eval oc_nc_1453)

lemma oc_nc_1454: "oc_sub None 1454"
  by (oc_eval oc_nc_1454)

lemma oc_nc_1455: "oc_sub None 1455"
  by (oc_eval oc_nc_1455)

lemma upt_nc_090: "[1440..<1456] = [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]"
  by (simp add: upt_rec)

lemma sec_nc_090: "\<forall>j\<in>{16 * 90..<16 * 90 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 90..<16 * 90 + 16}"
  then have "j \<in> set [1440..<1456]" unfolding set_upt by simp
  then have "j \<in> set [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]" unfolding upt_nc_090 .
  then show "oc_sub None j" using oc_nc_1440 oc_nc_1441 oc_nc_1442 oc_nc_1443 oc_nc_1444 oc_nc_1445 oc_nc_1446 oc_nc_1447 oc_nc_1448 oc_nc_1449 oc_nc_1450 oc_nc_1451 oc_nc_1452 oc_nc_1453 oc_nc_1454 oc_nc_1455
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
