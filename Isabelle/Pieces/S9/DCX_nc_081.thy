theory DCX_nc_081
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1296: "dc_sub None 1296"
  by (dc_eval dc_nc_1296)

lemma dc_nc_1297: "dc_sub None 1297"
  by (dc_eval dc_nc_1297)

lemma dc_nc_1298: "dc_sub None 1298"
  by (dc_eval dc_nc_1298)

lemma dc_nc_1299: "dc_sub None 1299"
  by (dc_eval dc_nc_1299)

lemma dc_nc_1300: "dc_sub None 1300"
  by (dc_eval dc_nc_1300)

lemma dc_nc_1301: "dc_sub None 1301"
  by (dc_eval dc_nc_1301)

lemma dc_nc_1302: "dc_sub None 1302"
  by (dc_eval dc_nc_1302)

lemma dc_nc_1303: "dc_sub None 1303"
  by (dc_eval dc_nc_1303)

lemma dc_nc_1304: "dc_sub None 1304"
  by (dc_eval dc_nc_1304)

lemma dc_nc_1305: "dc_sub None 1305"
  by (dc_eval dc_nc_1305)

lemma dc_nc_1306: "dc_sub None 1306"
  by (dc_eval dc_nc_1306)

lemma dc_nc_1307: "dc_sub None 1307"
  by (dc_eval dc_nc_1307)

lemma dc_nc_1308: "dc_sub None 1308"
  by (dc_eval dc_nc_1308)

lemma dc_nc_1309: "dc_sub None 1309"
  by (dc_eval dc_nc_1309)

lemma dc_nc_1310: "dc_sub None 1310"
  by (dc_eval dc_nc_1310)

lemma dc_nc_1311: "dc_sub None 1311"
  by (dc_eval dc_nc_1311)

lemma upt_nc_081: "[1296..<1312] = [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]"
  by (simp add: upt_rec)

lemma sec_nc_081: "\<forall>j\<in>{16 * 81..<16 * 81 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 81..<16 * 81 + 16}"
  then have "j \<in> set [1296..<1312]" unfolding set_upt by simp
  then have "j \<in> set [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]" unfolding upt_nc_081 .
  then show "dc_sub None j" using dc_nc_1296 dc_nc_1297 dc_nc_1298 dc_nc_1299 dc_nc_1300 dc_nc_1301 dc_nc_1302 dc_nc_1303 dc_nc_1304 dc_nc_1305 dc_nc_1306 dc_nc_1307 dc_nc_1308 dc_nc_1309 dc_nc_1310 dc_nc_1311
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
