theory OCX_c30_085
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1360: "oc_sub oc_b30 1360"
  by (oc_eval oc_c30_1360)

lemma oc_c30_1361: "oc_sub oc_b30 1361"
  by (oc_eval oc_c30_1361)

lemma oc_c30_1362: "oc_sub oc_b30 1362"
  by (oc_eval oc_c30_1362)

lemma oc_c30_1363: "oc_sub oc_b30 1363"
  by (oc_eval oc_c30_1363)

lemma oc_c30_1364: "oc_sub oc_b30 1364"
  by (oc_eval oc_c30_1364)

lemma oc_c30_1365: "oc_sub oc_b30 1365"
  by (oc_eval oc_c30_1365)

lemma oc_c30_1366: "oc_sub oc_b30 1366"
  by (oc_eval oc_c30_1366)

lemma oc_c30_1367: "oc_sub oc_b30 1367"
  by (oc_eval oc_c30_1367)

lemma oc_c30_1368: "oc_sub oc_b30 1368"
  by (oc_eval oc_c30_1368)

lemma oc_c30_1369: "oc_sub oc_b30 1369"
  by (oc_eval oc_c30_1369)

lemma oc_c30_1370: "oc_sub oc_b30 1370"
  by (oc_eval oc_c30_1370)

lemma oc_c30_1371: "oc_sub oc_b30 1371"
  by (oc_eval oc_c30_1371)

lemma oc_c30_1372: "oc_sub oc_b30 1372"
  by (oc_eval oc_c30_1372)

lemma oc_c30_1373: "oc_sub oc_b30 1373"
  by (oc_eval oc_c30_1373)

lemma oc_c30_1374: "oc_sub oc_b30 1374"
  by (oc_eval oc_c30_1374)

lemma oc_c30_1375: "oc_sub oc_b30 1375"
  by (oc_eval oc_c30_1375)

lemma upt_c30_085: "[1360..<1376] = [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]"
  by (simp add: upt_rec)

lemma sec_c30_085: "\<forall>j\<in>{16 * 85..<16 * 85 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 85..<16 * 85 + 16}"
  then have "j \<in> set [1360..<1376]" unfolding set_upt by simp
  then have "j \<in> set [1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375]" unfolding upt_c30_085 .
  then show "oc_sub oc_b30 j" using oc_c30_1360 oc_c30_1361 oc_c30_1362 oc_c30_1363 oc_c30_1364 oc_c30_1365 oc_c30_1366 oc_c30_1367 oc_c30_1368 oc_c30_1369 oc_c30_1370 oc_c30_1371 oc_c30_1372 oc_c30_1373 oc_c30_1374 oc_c30_1375
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
