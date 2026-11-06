theory OCX_c30_081
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1296: "oc_sub oc_b30 1296"
  by (oc_eval oc_c30_1296)

lemma oc_c30_1297: "oc_sub oc_b30 1297"
  by (oc_eval oc_c30_1297)

lemma oc_c30_1298: "oc_sub oc_b30 1298"
  by (oc_eval oc_c30_1298)

lemma oc_c30_1299: "oc_sub oc_b30 1299"
  by (oc_eval oc_c30_1299)

lemma oc_c30_1300: "oc_sub oc_b30 1300"
  by (oc_eval oc_c30_1300)

lemma oc_c30_1301: "oc_sub oc_b30 1301"
  by (oc_eval oc_c30_1301)

lemma oc_c30_1302: "oc_sub oc_b30 1302"
  by (oc_eval oc_c30_1302)

lemma oc_c30_1303: "oc_sub oc_b30 1303"
  by (oc_eval oc_c30_1303)

lemma oc_c30_1304: "oc_sub oc_b30 1304"
  by (oc_eval oc_c30_1304)

lemma oc_c30_1305: "oc_sub oc_b30 1305"
  by (oc_eval oc_c30_1305)

lemma oc_c30_1306: "oc_sub oc_b30 1306"
  by (oc_eval oc_c30_1306)

lemma oc_c30_1307: "oc_sub oc_b30 1307"
  by (oc_eval oc_c30_1307)

lemma oc_c30_1308: "oc_sub oc_b30 1308"
  by (oc_eval oc_c30_1308)

lemma oc_c30_1309: "oc_sub oc_b30 1309"
  by (oc_eval oc_c30_1309)

lemma oc_c30_1310: "oc_sub oc_b30 1310"
  by (oc_eval oc_c30_1310)

lemma oc_c30_1311: "oc_sub oc_b30 1311"
  by (oc_eval oc_c30_1311)

lemma upt_c30_081: "[1296..<1312] = [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]"
  by (simp add: upt_rec)

lemma sec_c30_081: "\<forall>j\<in>{16 * 81..<16 * 81 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 81..<16 * 81 + 16}"
  then have "j \<in> set [1296..<1312]" unfolding set_upt by simp
  then have "j \<in> set [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]" unfolding upt_c30_081 .
  then show "oc_sub oc_b30 j" using oc_c30_1296 oc_c30_1297 oc_c30_1298 oc_c30_1299 oc_c30_1300 oc_c30_1301 oc_c30_1302 oc_c30_1303 oc_c30_1304 oc_c30_1305 oc_c30_1306 oc_c30_1307 oc_c30_1308 oc_c30_1309 oc_c30_1310 oc_c30_1311
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
