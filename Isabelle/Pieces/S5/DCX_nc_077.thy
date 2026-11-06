theory DCX_nc_077
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1232: "dc_sub None 1232"
  by (dc_eval dc_nc_1232)

lemma dc_nc_1233: "dc_sub None 1233"
  by (dc_eval dc_nc_1233)

lemma dc_nc_1234: "dc_sub None 1234"
  by (dc_eval dc_nc_1234)

lemma dc_nc_1235: "dc_sub None 1235"
  by (dc_eval dc_nc_1235)

lemma dc_nc_1236: "dc_sub None 1236"
  by (dc_eval dc_nc_1236)

lemma dc_nc_1237: "dc_sub None 1237"
  by (dc_eval dc_nc_1237)

lemma dc_nc_1238: "dc_sub None 1238"
  by (dc_eval dc_nc_1238)

lemma dc_nc_1239: "dc_sub None 1239"
  by (dc_eval dc_nc_1239)

lemma dc_nc_1240: "dc_sub None 1240"
  by (dc_eval dc_nc_1240)

lemma dc_nc_1241: "dc_sub None 1241"
  by (dc_eval dc_nc_1241)

lemma dc_nc_1242: "dc_sub None 1242"
  by (dc_eval dc_nc_1242)

lemma dc_nc_1243: "dc_sub None 1243"
  by (dc_eval dc_nc_1243)

lemma dc_nc_1244: "dc_sub None 1244"
  by (dc_eval dc_nc_1244)

lemma dc_nc_1245: "dc_sub None 1245"
  by (dc_eval dc_nc_1245)

lemma dc_nc_1246: "dc_sub None 1246"
  by (dc_eval dc_nc_1246)

lemma dc_nc_1247: "dc_sub None 1247"
  by (dc_eval dc_nc_1247)

lemma upt_nc_077: "[1232..<1248] = [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]"
  by (simp add: upt_rec)

lemma sec_nc_077: "\<forall>j\<in>{16 * 77..<16 * 77 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 77..<16 * 77 + 16}"
  then have "j \<in> set [1232..<1248]" unfolding set_upt by simp
  then have "j \<in> set [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]" unfolding upt_nc_077 .
  then show "dc_sub None j" using dc_nc_1232 dc_nc_1233 dc_nc_1234 dc_nc_1235 dc_nc_1236 dc_nc_1237 dc_nc_1238 dc_nc_1239 dc_nc_1240 dc_nc_1241 dc_nc_1242 dc_nc_1243 dc_nc_1244 dc_nc_1245 dc_nc_1246 dc_nc_1247
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
