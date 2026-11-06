theory OCX_nc_077
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1232: "oc_sub None 1232"
  by (oc_eval oc_nc_1232)

lemma oc_nc_1233: "oc_sub None 1233"
  by (oc_eval oc_nc_1233)

lemma oc_nc_1234: "oc_sub None 1234"
  by (oc_eval oc_nc_1234)

lemma oc_nc_1235: "oc_sub None 1235"
  by (oc_eval oc_nc_1235)

lemma oc_nc_1236: "oc_sub None 1236"
  by (oc_eval oc_nc_1236)

lemma oc_nc_1237: "oc_sub None 1237"
  by (oc_eval oc_nc_1237)

lemma oc_nc_1238: "oc_sub None 1238"
  by (oc_eval oc_nc_1238)

lemma oc_nc_1239: "oc_sub None 1239"
  by (oc_eval oc_nc_1239)

lemma oc_nc_1240: "oc_sub None 1240"
  by (oc_eval oc_nc_1240)

lemma oc_nc_1241: "oc_sub None 1241"
  by (oc_eval oc_nc_1241)

lemma oc_nc_1242: "oc_sub None 1242"
  by (oc_eval oc_nc_1242)

lemma oc_nc_1243: "oc_sub None 1243"
  by (oc_eval oc_nc_1243)

lemma oc_nc_1244: "oc_sub None 1244"
  by (oc_eval oc_nc_1244)

lemma oc_nc_1245: "oc_sub None 1245"
  by (oc_eval oc_nc_1245)

lemma oc_nc_1246: "oc_sub None 1246"
  by (oc_eval oc_nc_1246)

lemma oc_nc_1247: "oc_sub None 1247"
  by (oc_eval oc_nc_1247)

lemma upt_nc_077: "[1232..<1248] = [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]"
  by (simp add: upt_rec)

lemma sec_nc_077: "\<forall>j\<in>{16 * 77..<16 * 77 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 77..<16 * 77 + 16}"
  then have "j \<in> set [1232..<1248]" unfolding set_upt by simp
  then have "j \<in> set [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]" unfolding upt_nc_077 .
  then show "oc_sub None j" using oc_nc_1232 oc_nc_1233 oc_nc_1234 oc_nc_1235 oc_nc_1236 oc_nc_1237 oc_nc_1238 oc_nc_1239 oc_nc_1240 oc_nc_1241 oc_nc_1242 oc_nc_1243 oc_nc_1244 oc_nc_1245 oc_nc_1246 oc_nc_1247
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
