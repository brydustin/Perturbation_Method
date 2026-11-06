theory DCX_nc_090
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1440: "dc_sub None 1440"
  by (dc_eval dc_nc_1440)

lemma dc_nc_1441: "dc_sub None 1441"
  by (dc_eval dc_nc_1441)

lemma dc_nc_1442: "dc_sub None 1442"
  by (dc_eval dc_nc_1442)

lemma dc_nc_1443: "dc_sub None 1443"
  by (dc_eval dc_nc_1443)

lemma dc_nc_1444: "dc_sub None 1444"
  by (dc_eval dc_nc_1444)

lemma dc_nc_1445: "dc_sub None 1445"
  by (dc_eval dc_nc_1445)

lemma dc_nc_1446: "dc_sub None 1446"
  by (dc_eval dc_nc_1446)

lemma dc_nc_1447: "dc_sub None 1447"
  by (dc_eval dc_nc_1447)

lemma dc_nc_1448: "dc_sub None 1448"
  by (dc_eval dc_nc_1448)

lemma dc_nc_1449: "dc_sub None 1449"
  by (dc_eval dc_nc_1449)

lemma dc_nc_1450: "dc_sub None 1450"
  by (dc_eval dc_nc_1450)

lemma dc_nc_1451: "dc_sub None 1451"
  by (dc_eval dc_nc_1451)

lemma dc_nc_1452: "dc_sub None 1452"
  by (dc_eval dc_nc_1452)

lemma dc_nc_1453: "dc_sub None 1453"
  by (dc_eval dc_nc_1453)

lemma dc_nc_1454: "dc_sub None 1454"
  by (dc_eval dc_nc_1454)

lemma dc_nc_1455: "dc_sub None 1455"
  by (dc_eval dc_nc_1455)

lemma upt_nc_090: "[1440..<1456] = [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]"
  by (simp add: upt_rec)

lemma sec_nc_090: "\<forall>j\<in>{16 * 90..<16 * 90 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 90..<16 * 90 + 16}"
  then have "j \<in> set [1440..<1456]" unfolding set_upt by simp
  then have "j \<in> set [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]" unfolding upt_nc_090 .
  then show "dc_sub None j" using dc_nc_1440 dc_nc_1441 dc_nc_1442 dc_nc_1443 dc_nc_1444 dc_nc_1445 dc_nc_1446 dc_nc_1447 dc_nc_1448 dc_nc_1449 dc_nc_1450 dc_nc_1451 dc_nc_1452 dc_nc_1453 dc_nc_1454 dc_nc_1455
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
