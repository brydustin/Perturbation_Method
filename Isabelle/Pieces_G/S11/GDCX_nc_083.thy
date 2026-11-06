theory GDCX_nc_083
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1328: "gdc_sub None 1328"
  by (gdc_eval gdc_nc_1328)

lemma gdc_nc_1329: "gdc_sub None 1329"
  by (gdc_eval gdc_nc_1329)

lemma gdc_nc_1330: "gdc_sub None 1330"
  by (gdc_eval gdc_nc_1330)

lemma gdc_nc_1331: "gdc_sub None 1331"
  by (gdc_eval gdc_nc_1331)

lemma gdc_nc_1332: "gdc_sub None 1332"
  by (gdc_eval gdc_nc_1332)

lemma gdc_nc_1333: "gdc_sub None 1333"
  by (gdc_eval gdc_nc_1333)

lemma gdc_nc_1334: "gdc_sub None 1334"
  by (gdc_eval gdc_nc_1334)

lemma gdc_nc_1335: "gdc_sub None 1335"
  by (gdc_eval gdc_nc_1335)

lemma gdc_nc_1336: "gdc_sub None 1336"
  by (gdc_eval gdc_nc_1336)

lemma gdc_nc_1337: "gdc_sub None 1337"
  by (gdc_eval gdc_nc_1337)

lemma gdc_nc_1338: "gdc_sub None 1338"
  by (gdc_eval gdc_nc_1338)

lemma gdc_nc_1339: "gdc_sub None 1339"
  by (gdc_eval gdc_nc_1339)

lemma gdc_nc_1340: "gdc_sub None 1340"
  by (gdc_eval gdc_nc_1340)

lemma gdc_nc_1341: "gdc_sub None 1341"
  by (gdc_eval gdc_nc_1341)

lemma gdc_nc_1342: "gdc_sub None 1342"
  by (gdc_eval gdc_nc_1342)

lemma gdc_nc_1343: "gdc_sub None 1343"
  by (gdc_eval gdc_nc_1343)

lemma gupt_nc_083: "[1328..<1344] = [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]"
  by (simp add: upt_rec)

lemma gsec_nc_083: "\<forall>j\<in>{16 * 83..<16 * 83 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 83..<16 * 83 + 16}"
  then have "j \<in> set [1328..<1344]" unfolding set_upt by simp
  then have "j \<in> set [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]" unfolding gupt_nc_083 .
  then show "gdc_sub None j" using gdc_nc_1328 gdc_nc_1329 gdc_nc_1330 gdc_nc_1331 gdc_nc_1332 gdc_nc_1333 gdc_nc_1334 gdc_nc_1335 gdc_nc_1336 gdc_nc_1337 gdc_nc_1338 gdc_nc_1339 gdc_nc_1340 gdc_nc_1341 gdc_nc_1342 gdc_nc_1343
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
