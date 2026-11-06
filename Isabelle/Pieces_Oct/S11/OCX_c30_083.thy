theory OCX_c30_083
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1328: "oc_sub oc_b30 1328"
  by (oc_eval oc_c30_1328)

lemma oc_c30_1329: "oc_sub oc_b30 1329"
  by (oc_eval oc_c30_1329)

lemma oc_c30_1330: "oc_sub oc_b30 1330"
  by (oc_eval oc_c30_1330)

lemma oc_c30_1331: "oc_sub oc_b30 1331"
  by (oc_eval oc_c30_1331)

lemma oc_c30_1332: "oc_sub oc_b30 1332"
  by (oc_eval oc_c30_1332)

lemma oc_c30_1333: "oc_sub oc_b30 1333"
  by (oc_eval oc_c30_1333)

lemma oc_c30_1334: "oc_sub oc_b30 1334"
  by (oc_eval oc_c30_1334)

lemma oc_c30_1335: "oc_sub oc_b30 1335"
  by (oc_eval oc_c30_1335)

lemma oc_c30_1336: "oc_sub oc_b30 1336"
  by (oc_eval oc_c30_1336)

lemma oc_c30_1337: "oc_sub oc_b30 1337"
  by (oc_eval oc_c30_1337)

lemma oc_c30_1338: "oc_sub oc_b30 1338"
  by (oc_eval oc_c30_1338)

lemma oc_c30_1339: "oc_sub oc_b30 1339"
  by (oc_eval oc_c30_1339)

lemma oc_c30_1340: "oc_sub oc_b30 1340"
  by (oc_eval oc_c30_1340)

lemma oc_c30_1341: "oc_sub oc_b30 1341"
  by (oc_eval oc_c30_1341)

lemma oc_c30_1342: "oc_sub oc_b30 1342"
  by (oc_eval oc_c30_1342)

lemma oc_c30_1343: "oc_sub oc_b30 1343"
  by (oc_eval oc_c30_1343)

lemma upt_c30_083: "[1328..<1344] = [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]"
  by (simp add: upt_rec)

lemma sec_c30_083: "\<forall>j\<in>{16 * 83..<16 * 83 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 83..<16 * 83 + 16}"
  then have "j \<in> set [1328..<1344]" unfolding set_upt by simp
  then have "j \<in> set [1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343]" unfolding upt_c30_083 .
  then show "oc_sub oc_b30 j" using oc_c30_1328 oc_c30_1329 oc_c30_1330 oc_c30_1331 oc_c30_1332 oc_c30_1333 oc_c30_1334 oc_c30_1335 oc_c30_1336 oc_c30_1337 oc_c30_1338 oc_c30_1339 oc_c30_1340 oc_c30_1341 oc_c30_1342 oc_c30_1343
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
