theory GDCX_nc_077
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1232: "gdc_sub None 1232"
  by (gdc_eval gdc_nc_1232)

lemma gdc_nc_1233: "gdc_sub None 1233"
  by (gdc_eval gdc_nc_1233)

lemma gdc_nc_1234: "gdc_sub None 1234"
  by (gdc_eval gdc_nc_1234)

lemma gdc_nc_1235: "gdc_sub None 1235"
  by (gdc_eval gdc_nc_1235)

lemma gdc_nc_1236: "gdc_sub None 1236"
  by (gdc_eval gdc_nc_1236)

lemma gdc_nc_1237: "gdc_sub None 1237"
  by (gdc_eval gdc_nc_1237)

lemma gdc_nc_1238: "gdc_sub None 1238"
  by (gdc_eval gdc_nc_1238)

lemma gdc_nc_1239: "gdc_sub None 1239"
  by (gdc_eval gdc_nc_1239)

lemma gdc_nc_1240: "gdc_sub None 1240"
  by (gdc_eval gdc_nc_1240)

lemma gdc_nc_1241: "gdc_sub None 1241"
  by (gdc_eval gdc_nc_1241)

lemma gdc_nc_1242: "gdc_sub None 1242"
  by (gdc_eval gdc_nc_1242)

lemma gdc_nc_1243: "gdc_sub None 1243"
  by (gdc_eval gdc_nc_1243)

lemma gdc_nc_1244: "gdc_sub None 1244"
  by (gdc_eval gdc_nc_1244)

lemma gdc_nc_1245: "gdc_sub None 1245"
  by (gdc_eval gdc_nc_1245)

lemma gdc_nc_1246: "gdc_sub None 1246"
  by (gdc_eval gdc_nc_1246)

lemma gdc_nc_1247: "gdc_sub None 1247"
  by (gdc_eval gdc_nc_1247)

lemma gupt_nc_077: "[1232..<1248] = [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]"
  by (simp add: upt_rec)

lemma gsec_nc_077: "\<forall>j\<in>{16 * 77..<16 * 77 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 77..<16 * 77 + 16}"
  then have "j \<in> set [1232..<1248]" unfolding set_upt by simp
  then have "j \<in> set [1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247]" unfolding gupt_nc_077 .
  then show "gdc_sub None j" using gdc_nc_1232 gdc_nc_1233 gdc_nc_1234 gdc_nc_1235 gdc_nc_1236 gdc_nc_1237 gdc_nc_1238 gdc_nc_1239 gdc_nc_1240 gdc_nc_1241 gdc_nc_1242 gdc_nc_1243 gdc_nc_1244 gdc_nc_1245 gdc_nc_1246 gdc_nc_1247
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
