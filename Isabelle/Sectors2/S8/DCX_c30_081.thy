theory DCX_c30_081
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1296: "dc_sub dc_b30 1296"
  by (dc_eval dc_c30_1296)

lemma dc_c30_1297: "dc_sub dc_b30 1297"
  by (dc_eval dc_c30_1297)

lemma dc_c30_1298: "dc_sub dc_b30 1298"
  by (dc_eval dc_c30_1298)

lemma dc_c30_1299: "dc_sub dc_b30 1299"
  by (dc_eval dc_c30_1299)

lemma dc_c30_1300: "dc_sub dc_b30 1300"
  by (dc_eval dc_c30_1300)

lemma dc_c30_1301: "dc_sub dc_b30 1301"
  by (dc_eval dc_c30_1301)

lemma dc_c30_1302: "dc_sub dc_b30 1302"
  by (dc_eval dc_c30_1302)

lemma dc_c30_1303: "dc_sub dc_b30 1303"
  by (dc_eval dc_c30_1303)

lemma dc_c30_1304: "dc_sub dc_b30 1304"
  by (dc_eval dc_c30_1304)

lemma dc_c30_1305: "dc_sub dc_b30 1305"
  by (dc_eval dc_c30_1305)

lemma dc_c30_1306: "dc_sub dc_b30 1306"
  by (dc_eval dc_c30_1306)

lemma dc_c30_1307: "dc_sub dc_b30 1307"
  by (dc_eval dc_c30_1307)

lemma dc_c30_1308: "dc_sub dc_b30 1308"
  by (dc_eval dc_c30_1308)

lemma dc_c30_1309: "dc_sub dc_b30 1309"
  by (dc_eval dc_c30_1309)

lemma dc_c30_1310: "dc_sub dc_b30 1310"
  by (dc_eval dc_c30_1310)

lemma dc_c30_1311: "dc_sub dc_b30 1311"
  by (dc_eval dc_c30_1311)

lemma upt_c30_081: "[1296..<1312] = [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]"
  by (simp add: upt_rec)

lemma sec_c30_081: "\<forall>j\<in>{16 * 81..<16 * 81 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 81..<16 * 81 + 16}"
  then have "j \<in> set [1296..<1312]" unfolding set_upt by simp
  then have "j \<in> set [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]" unfolding upt_c30_081 .
  then show "dc_sub dc_b30 j" using dc_c30_1296 dc_c30_1297 dc_c30_1298 dc_c30_1299 dc_c30_1300 dc_c30_1301 dc_c30_1302 dc_c30_1303 dc_c30_1304 dc_c30_1305 dc_c30_1306 dc_c30_1307 dc_c30_1308 dc_c30_1309 dc_c30_1310 dc_c30_1311
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
