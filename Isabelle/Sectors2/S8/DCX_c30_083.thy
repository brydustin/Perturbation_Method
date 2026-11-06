theory DCX_c30_083
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1328: "dc_sub dc_b30 1328"
  by (dc_eval dc_c30_1328)

lemma dc_c30_1329: "dc_sub dc_b30 1329"
  by (dc_eval dc_c30_1329)

lemma dc_c30_1330: "dc_sub dc_b30 1330"
  by (dc_eval dc_c30_1330)

lemma dc_c30_1331: "dc_sub dc_b30 1331"
  by (dc_eval dc_c30_1331)

lemma dc_c30_1332: "dc_sub dc_b30 1332"
  by (dc_eval dc_c30_1332)

lemma dc_c30_1333: "dc_sub dc_b30 1333"
  by (dc_eval dc_c30_1333)

lemma dc_c30_1334: "dc_sub dc_b30 1334"
  by (dc_eval dc_c30_1334)

lemma dc_c30_1335: "dc_sub dc_b30 1335"
  by (dc_eval dc_c30_1335)

lemma dc_c30_1336: "dc_sub dc_b30 1336"
  by (dc_eval dc_c30_1336)

lemma dc_c30_1337: "dc_sub dc_b30 1337"
  by (dc_eval dc_c30_1337)

lemma dc_c30_1338: "dc_sub dc_b30 1338"
  by (dc_eval dc_c30_1338)

lemma dc_c30_1339: "dc_sub dc_b30 1339"
  by (dc_eval dc_c30_1339)

lemma dc_c30_1340: "dc_sub dc_b30 1340"
  by (dc_eval dc_c30_1340)

lemma dc_c30_1341: "dc_sub dc_b30 1341"
  by (dc_eval dc_c30_1341)

lemma dc_c30_1342: "dc_sub dc_b30 1342"
  by (dc_eval dc_c30_1342)

lemma dc_c30_1343: "dc_sub dc_b30 1343"
  by (dc_eval dc_c30_1343)

lemma upt_c30_083: "[1328..<1344] = [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]"
  by (simp add: upt_rec)

lemma sec_c30_083: "\<forall>j\<in>{16 * 83..<16 * 83 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 83..<16 * 83 + 16}"
  then have "j \<in> set [1328..<1344]" unfolding set_upt by simp
  then have "j \<in> set [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]" unfolding upt_c30_083 .
  then show "dc_sub dc_b30 j" using dc_c30_1328 dc_c30_1329 dc_c30_1330 dc_c30_1331 dc_c30_1332 dc_c30_1333 dc_c30_1334 dc_c30_1335 dc_c30_1336 dc_c30_1337 dc_c30_1338 dc_c30_1339 dc_c30_1340 dc_c30_1341 dc_c30_1342 dc_c30_1343
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
