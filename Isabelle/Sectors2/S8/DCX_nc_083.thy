theory DCX_nc_083
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1328: "dc_sub None 1328"
  by (dc_eval dc_nc_1328)

lemma dc_nc_1329: "dc_sub None 1329"
  by (dc_eval dc_nc_1329)

lemma dc_nc_1330: "dc_sub None 1330"
  by (dc_eval dc_nc_1330)

lemma dc_nc_1331: "dc_sub None 1331"
  by (dc_eval dc_nc_1331)

lemma dc_nc_1332: "dc_sub None 1332"
  by (dc_eval dc_nc_1332)

lemma dc_nc_1333: "dc_sub None 1333"
  by (dc_eval dc_nc_1333)

lemma dc_nc_1334: "dc_sub None 1334"
  by (dc_eval dc_nc_1334)

lemma dc_nc_1335: "dc_sub None 1335"
  by (dc_eval dc_nc_1335)

lemma dc_nc_1336: "dc_sub None 1336"
  by (dc_eval dc_nc_1336)

lemma dc_nc_1337: "dc_sub None 1337"
  by (dc_eval dc_nc_1337)

lemma dc_nc_1338: "dc_sub None 1338"
  by (dc_eval dc_nc_1338)

lemma dc_nc_1339: "dc_sub None 1339"
  by (dc_eval dc_nc_1339)

lemma dc_nc_1340: "dc_sub None 1340"
  by (dc_eval dc_nc_1340)

lemma dc_nc_1341: "dc_sub None 1341"
  by (dc_eval dc_nc_1341)

lemma dc_nc_1342: "dc_sub None 1342"
  by (dc_eval dc_nc_1342)

lemma dc_nc_1343: "dc_sub None 1343"
  by (dc_eval dc_nc_1343)

lemma upt_nc_083: "[1328..<1344] = [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]"
  by (simp add: upt_rec)

lemma sec_nc_083: "\<forall>j\<in>{16 * 83..<16 * 83 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 83..<16 * 83 + 16}"
  then have "j \<in> set [1328..<1344]" unfolding set_upt by simp
  then have "j \<in> set [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]" unfolding upt_nc_083 .
  then show "dc_sub None j" using dc_nc_1328 dc_nc_1329 dc_nc_1330 dc_nc_1331 dc_nc_1332 dc_nc_1333 dc_nc_1334 dc_nc_1335 dc_nc_1336 dc_nc_1337 dc_nc_1338 dc_nc_1339 dc_nc_1340 dc_nc_1341 dc_nc_1342 dc_nc_1343
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
