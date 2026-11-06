theory GDCX_nc_081
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1296: "gdc_sub None 1296"
  by (gdc_eval gdc_nc_1296)

lemma gdc_nc_1297: "gdc_sub None 1297"
  by (gdc_eval gdc_nc_1297)

lemma gdc_nc_1298: "gdc_sub None 1298"
  by (gdc_eval gdc_nc_1298)

lemma gdc_nc_1299: "gdc_sub None 1299"
  by (gdc_eval gdc_nc_1299)

lemma gdc_nc_1300: "gdc_sub None 1300"
  by (gdc_eval gdc_nc_1300)

lemma gdc_nc_1301: "gdc_sub None 1301"
  by (gdc_eval gdc_nc_1301)

lemma gdc_nc_1302: "gdc_sub None 1302"
  by (gdc_eval gdc_nc_1302)

lemma gdc_nc_1303: "gdc_sub None 1303"
  by (gdc_eval gdc_nc_1303)

lemma gdc_nc_1304: "gdc_sub None 1304"
  by (gdc_eval gdc_nc_1304)

lemma gdc_nc_1305: "gdc_sub None 1305"
  by (gdc_eval gdc_nc_1305)

lemma gdc_nc_1306: "gdc_sub None 1306"
  by (gdc_eval gdc_nc_1306)

lemma gdc_nc_1307: "gdc_sub None 1307"
  by (gdc_eval gdc_nc_1307)

lemma gdc_nc_1308: "gdc_sub None 1308"
  by (gdc_eval gdc_nc_1308)

lemma gdc_nc_1309: "gdc_sub None 1309"
  by (gdc_eval gdc_nc_1309)

lemma gdc_nc_1310: "gdc_sub None 1310"
  by (gdc_eval gdc_nc_1310)

lemma gdc_nc_1311: "gdc_sub None 1311"
  by (gdc_eval gdc_nc_1311)

lemma gupt_nc_081: "[1296..<1312] = [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]"
  by (simp add: upt_rec)

lemma gsec_nc_081: "\<forall>j\<in>{16 * 81..<16 * 81 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 81..<16 * 81 + 16}"
  then have "j \<in> set [1296..<1312]" unfolding set_upt by simp
  then have "j \<in> set [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]" unfolding gupt_nc_081 .
  then show "gdc_sub None j" using gdc_nc_1296 gdc_nc_1297 gdc_nc_1298 gdc_nc_1299 gdc_nc_1300 gdc_nc_1301 gdc_nc_1302 gdc_nc_1303 gdc_nc_1304 gdc_nc_1305 gdc_nc_1306 gdc_nc_1307 gdc_nc_1308 gdc_nc_1309 gdc_nc_1310 gdc_nc_1311
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
