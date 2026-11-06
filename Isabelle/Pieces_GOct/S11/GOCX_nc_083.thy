theory GOCX_nc_083
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1328: "goc_sub None 1328"
  by (goc_eval goc_nc_1328)

lemma goc_nc_1329: "goc_sub None 1329"
  by (goc_eval goc_nc_1329)

lemma goc_nc_1330: "goc_sub None 1330"
  by (goc_eval goc_nc_1330)

lemma goc_nc_1331: "goc_sub None 1331"
  by (goc_eval goc_nc_1331)

lemma goc_nc_1332: "goc_sub None 1332"
  by (goc_eval goc_nc_1332)

lemma goc_nc_1333: "goc_sub None 1333"
  by (goc_eval goc_nc_1333)

lemma goc_nc_1334: "goc_sub None 1334"
  by (goc_eval goc_nc_1334)

lemma goc_nc_1335: "goc_sub None 1335"
  by (goc_eval goc_nc_1335)

lemma goc_nc_1336: "goc_sub None 1336"
  by (goc_eval goc_nc_1336)

lemma goc_nc_1337: "goc_sub None 1337"
  by (goc_eval goc_nc_1337)

lemma goc_nc_1338: "goc_sub None 1338"
  by (goc_eval goc_nc_1338)

lemma goc_nc_1339: "goc_sub None 1339"
  by (goc_eval goc_nc_1339)

lemma goc_nc_1340: "goc_sub None 1340"
  by (goc_eval goc_nc_1340)

lemma goc_nc_1341: "goc_sub None 1341"
  by (goc_eval goc_nc_1341)

lemma goc_nc_1342: "goc_sub None 1342"
  by (goc_eval goc_nc_1342)

lemma goc_nc_1343: "goc_sub None 1343"
  by (goc_eval goc_nc_1343)

lemma gupt_nc_083: "[1328..<1344] = [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]"
  by (simp add: upt_rec)

lemma gsec_nc_083: "\<forall>j\<in>{16 * 83..<16 * 83 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 83..<16 * 83 + 16}"
  then have "j \<in> set [1328..<1344]" unfolding set_upt by simp
  then have "j \<in> set [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]" unfolding gupt_nc_083 .
  then show "goc_sub None j" using goc_nc_1328 goc_nc_1329 goc_nc_1330 goc_nc_1331 goc_nc_1332 goc_nc_1333 goc_nc_1334 goc_nc_1335 goc_nc_1336 goc_nc_1337 goc_nc_1338 goc_nc_1339 goc_nc_1340 goc_nc_1341 goc_nc_1342 goc_nc_1343
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
