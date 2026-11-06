theory DCX_c30_077
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1232: "dc_sub dc_b30 1232"
  by (dc_eval dc_c30_1232)

lemma dc_c30_1233: "dc_sub dc_b30 1233"
  by (dc_eval dc_c30_1233)

lemma dc_c30_1234: "dc_sub dc_b30 1234"
  by (dc_eval dc_c30_1234)

lemma dc_c30_1235: "dc_sub dc_b30 1235"
  by (dc_eval dc_c30_1235)

lemma dc_c30_1236: "dc_sub dc_b30 1236"
  by (dc_eval dc_c30_1236)

lemma dc_c30_1237: "dc_sub dc_b30 1237"
  by (dc_eval dc_c30_1237)

lemma dc_c30_1238: "dc_sub dc_b30 1238"
  by (dc_eval dc_c30_1238)

lemma dc_c30_1239: "dc_sub dc_b30 1239"
  by (dc_eval dc_c30_1239)

lemma dc_c30_1240: "dc_sub dc_b30 1240"
  by (dc_eval dc_c30_1240)

lemma dc_c30_1241: "dc_sub dc_b30 1241"
  by (dc_eval dc_c30_1241)

lemma dc_c30_1242: "dc_sub dc_b30 1242"
  by (dc_eval dc_c30_1242)

lemma dc_c30_1243: "dc_sub dc_b30 1243"
  by (dc_eval dc_c30_1243)

lemma dc_c30_1244: "dc_sub dc_b30 1244"
  by (dc_eval dc_c30_1244)

lemma dc_c30_1245: "dc_sub dc_b30 1245"
  by (dc_eval dc_c30_1245)

lemma dc_c30_1246: "dc_sub dc_b30 1246"
  by (dc_eval dc_c30_1246)

lemma dc_c30_1247: "dc_sub dc_b30 1247"
  by (dc_eval dc_c30_1247)

lemma upt_c30_077: "[1232..<1248] = [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]"
  by (simp add: upt_rec)

lemma sec_c30_077: "\<forall>j\<in>{16 * 77..<16 * 77 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 77..<16 * 77 + 16}"
  then have "j \<in> set [1232..<1248]" unfolding set_upt by simp
  then have "j \<in> set [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]" unfolding upt_c30_077 .
  then show "dc_sub dc_b30 j" using dc_c30_1232 dc_c30_1233 dc_c30_1234 dc_c30_1235 dc_c30_1236 dc_c30_1237 dc_c30_1238 dc_c30_1239 dc_c30_1240 dc_c30_1241 dc_c30_1242 dc_c30_1243 dc_c30_1244 dc_c30_1245 dc_c30_1246 dc_c30_1247
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
