theory GOCX_nc_077
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1232: "goc_sub None 1232"
  by (goc_eval goc_nc_1232)

lemma goc_nc_1233: "goc_sub None 1233"
  by (goc_eval goc_nc_1233)

lemma goc_nc_1234: "goc_sub None 1234"
  by (goc_eval goc_nc_1234)

lemma goc_nc_1235: "goc_sub None 1235"
  by (goc_eval goc_nc_1235)

lemma goc_nc_1236: "goc_sub None 1236"
  by (goc_eval goc_nc_1236)

lemma goc_nc_1237: "goc_sub None 1237"
  by (goc_eval goc_nc_1237)

lemma goc_nc_1238: "goc_sub None 1238"
  by (goc_eval goc_nc_1238)

lemma goc_nc_1239: "goc_sub None 1239"
  by (goc_eval goc_nc_1239)

lemma goc_nc_1240: "goc_sub None 1240"
  by (goc_eval goc_nc_1240)

lemma goc_nc_1241: "goc_sub None 1241"
  by (goc_eval goc_nc_1241)

lemma goc_nc_1242: "goc_sub None 1242"
  by (goc_eval goc_nc_1242)

lemma goc_nc_1243: "goc_sub None 1243"
  by (goc_eval goc_nc_1243)

lemma goc_nc_1244: "goc_sub None 1244"
  by (goc_eval goc_nc_1244)

lemma goc_nc_1245: "goc_sub None 1245"
  by (goc_eval goc_nc_1245)

lemma goc_nc_1246: "goc_sub None 1246"
  by (goc_eval goc_nc_1246)

lemma goc_nc_1247: "goc_sub None 1247"
  by (goc_eval goc_nc_1247)

lemma gupt_nc_077: "[1232..<1248] = [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]"
  by (simp add: upt_rec)

lemma gsec_nc_077: "\<forall>j\<in>{16 * 77..<16 * 77 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 77..<16 * 77 + 16}"
  then have "j \<in> set [1232..<1248]" unfolding set_upt by simp
  then have "j \<in> set [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]" unfolding gupt_nc_077 .
  then show "goc_sub None j" using goc_nc_1232 goc_nc_1233 goc_nc_1234 goc_nc_1235 goc_nc_1236 goc_nc_1237 goc_nc_1238 goc_nc_1239 goc_nc_1240 goc_nc_1241 goc_nc_1242 goc_nc_1243 goc_nc_1244 goc_nc_1245 goc_nc_1246 goc_nc_1247
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
