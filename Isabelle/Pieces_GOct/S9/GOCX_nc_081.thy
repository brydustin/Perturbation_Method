theory GOCX_nc_081
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1296: "goc_sub None 1296"
  by (goc_eval goc_nc_1296)

lemma goc_nc_1297: "goc_sub None 1297"
  by (goc_eval goc_nc_1297)

lemma goc_nc_1298: "goc_sub None 1298"
  by (goc_eval goc_nc_1298)

lemma goc_nc_1299: "goc_sub None 1299"
  by (goc_eval goc_nc_1299)

lemma goc_nc_1300: "goc_sub None 1300"
  by (goc_eval goc_nc_1300)

lemma goc_nc_1301: "goc_sub None 1301"
  by (goc_eval goc_nc_1301)

lemma goc_nc_1302: "goc_sub None 1302"
  by (goc_eval goc_nc_1302)

lemma goc_nc_1303: "goc_sub None 1303"
  by (goc_eval goc_nc_1303)

lemma goc_nc_1304: "goc_sub None 1304"
  by (goc_eval goc_nc_1304)

lemma goc_nc_1305: "goc_sub None 1305"
  by (goc_eval goc_nc_1305)

lemma goc_nc_1306: "goc_sub None 1306"
  by (goc_eval goc_nc_1306)

lemma goc_nc_1307: "goc_sub None 1307"
  by (goc_eval goc_nc_1307)

lemma goc_nc_1308: "goc_sub None 1308"
  by (goc_eval goc_nc_1308)

lemma goc_nc_1309: "goc_sub None 1309"
  by (goc_eval goc_nc_1309)

lemma goc_nc_1310: "goc_sub None 1310"
  by (goc_eval goc_nc_1310)

lemma goc_nc_1311: "goc_sub None 1311"
  by (goc_eval goc_nc_1311)

lemma gupt_nc_081: "[1296..<1312] = [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]"
  by (simp add: upt_rec)

lemma gsec_nc_081: "\<forall>j\<in>{16 * 81..<16 * 81 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 81..<16 * 81 + 16}"
  then have "j \<in> set [1296..<1312]" unfolding set_upt by simp
  then have "j \<in> set [1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311]" unfolding gupt_nc_081 .
  then show "goc_sub None j" using goc_nc_1296 goc_nc_1297 goc_nc_1298 goc_nc_1299 goc_nc_1300 goc_nc_1301 goc_nc_1302 goc_nc_1303 goc_nc_1304 goc_nc_1305 goc_nc_1306 goc_nc_1307 goc_nc_1308 goc_nc_1309 goc_nc_1310 goc_nc_1311
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
