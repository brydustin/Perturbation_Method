theory OCX_c30_077
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1232: "oc_sub oc_b30 1232"
  by (oc_eval oc_c30_1232)

lemma oc_c30_1233: "oc_sub oc_b30 1233"
  by (oc_eval oc_c30_1233)

lemma oc_c30_1234: "oc_sub oc_b30 1234"
  by (oc_eval oc_c30_1234)

lemma oc_c30_1235: "oc_sub oc_b30 1235"
  by (oc_eval oc_c30_1235)

lemma oc_c30_1236: "oc_sub oc_b30 1236"
  by (oc_eval oc_c30_1236)

lemma oc_c30_1237: "oc_sub oc_b30 1237"
  by (oc_eval oc_c30_1237)

lemma oc_c30_1238: "oc_sub oc_b30 1238"
  by (oc_eval oc_c30_1238)

lemma oc_c30_1239: "oc_sub oc_b30 1239"
  by (oc_eval oc_c30_1239)

lemma oc_c30_1240: "oc_sub oc_b30 1240"
  by (oc_eval oc_c30_1240)

lemma oc_c30_1241: "oc_sub oc_b30 1241"
  by (oc_eval oc_c30_1241)

lemma oc_c30_1242: "oc_sub oc_b30 1242"
  by (oc_eval oc_c30_1242)

lemma oc_c30_1243: "oc_sub oc_b30 1243"
  by (oc_eval oc_c30_1243)

lemma oc_c30_1244: "oc_sub oc_b30 1244"
  by (oc_eval oc_c30_1244)

lemma oc_c30_1245: "oc_sub oc_b30 1245"
  by (oc_eval oc_c30_1245)

lemma oc_c30_1246: "oc_sub oc_b30 1246"
  by (oc_eval oc_c30_1246)

lemma oc_c30_1247: "oc_sub oc_b30 1247"
  by (oc_eval oc_c30_1247)

lemma upt_c30_077: "[1232..<1248] = [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]"
  by (simp add: upt_rec)

lemma sec_c30_077: "\<forall>j\<in>{16 * 77..<16 * 77 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 77..<16 * 77 + 16}"
  then have "j \<in> set [1232..<1248]" unfolding set_upt by simp
  then have "j \<in> set [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]" unfolding upt_c30_077 .
  then show "oc_sub oc_b30 j" using oc_c30_1232 oc_c30_1233 oc_c30_1234 oc_c30_1235 oc_c30_1236 oc_c30_1237 oc_c30_1238 oc_c30_1239 oc_c30_1240 oc_c30_1241 oc_c30_1242 oc_c30_1243 oc_c30_1244 oc_c30_1245 oc_c30_1246 oc_c30_1247
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
