theory GDCX_nc_090
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1440: "gdc_sub None 1440"
  by (gdc_eval gdc_nc_1440)

lemma gdc_nc_1441: "gdc_sub None 1441"
  by (gdc_eval gdc_nc_1441)

lemma gdc_nc_1442: "gdc_sub None 1442"
  by (gdc_eval gdc_nc_1442)

lemma gdc_nc_1443: "gdc_sub None 1443"
  by (gdc_eval gdc_nc_1443)

lemma gdc_nc_1444: "gdc_sub None 1444"
  by (gdc_eval gdc_nc_1444)

lemma gdc_nc_1445: "gdc_sub None 1445"
  by (gdc_eval gdc_nc_1445)

lemma gdc_nc_1446: "gdc_sub None 1446"
  by (gdc_eval gdc_nc_1446)

lemma gdc_nc_1447: "gdc_sub None 1447"
  by (gdc_eval gdc_nc_1447)

lemma gdc_nc_1448: "gdc_sub None 1448"
  by (gdc_eval gdc_nc_1448)

lemma gdc_nc_1449: "gdc_sub None 1449"
  by (gdc_eval gdc_nc_1449)

lemma gdc_nc_1450: "gdc_sub None 1450"
  by (gdc_eval gdc_nc_1450)

lemma gdc_nc_1451: "gdc_sub None 1451"
  by (gdc_eval gdc_nc_1451)

lemma gdc_nc_1452: "gdc_sub None 1452"
  by (gdc_eval gdc_nc_1452)

lemma gdc_nc_1453: "gdc_sub None 1453"
  by (gdc_eval gdc_nc_1453)

lemma gdc_nc_1454: "gdc_sub None 1454"
  by (gdc_eval gdc_nc_1454)

lemma gdc_nc_1455: "gdc_sub None 1455"
  by (gdc_eval gdc_nc_1455)

lemma gupt_nc_090: "[1440..<1456] = [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]"
  by (simp add: upt_rec)

lemma gsec_nc_090: "\<forall>j\<in>{16 * 90..<16 * 90 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 90..<16 * 90 + 16}"
  then have "j \<in> set [1440..<1456]" unfolding set_upt by simp
  then have "j \<in> set [1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455]" unfolding gupt_nc_090 .
  then show "gdc_sub None j" using gdc_nc_1440 gdc_nc_1441 gdc_nc_1442 gdc_nc_1443 gdc_nc_1444 gdc_nc_1445 gdc_nc_1446 gdc_nc_1447 gdc_nc_1448 gdc_nc_1449 gdc_nc_1450 gdc_nc_1451 gdc_nc_1452 gdc_nc_1453 gdc_nc_1454 gdc_nc_1455
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
