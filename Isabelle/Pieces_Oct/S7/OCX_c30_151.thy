theory OCX_c30_151
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2416: "oc_sub oc_b30 2416"
  by (oc_eval oc_c30_2416)

lemma oc_c30_2417: "oc_sub oc_b30 2417"
  by (oc_eval oc_c30_2417)

lemma oc_c30_2418: "oc_sub oc_b30 2418"
  by (oc_eval oc_c30_2418)

lemma oc_c30_2419: "oc_sub oc_b30 2419"
  by (oc_eval oc_c30_2419)

lemma oc_c30_2420: "oc_sub oc_b30 2420"
  by (oc_eval oc_c30_2420)

lemma oc_c30_2421: "oc_sub oc_b30 2421"
  by (oc_eval oc_c30_2421)

lemma oc_c30_2422: "oc_sub oc_b30 2422"
  by (oc_eval oc_c30_2422)

lemma oc_c30_2423: "oc_sub oc_b30 2423"
  by (oc_eval oc_c30_2423)

lemma oc_c30_2424: "oc_sub oc_b30 2424"
  by (oc_eval oc_c30_2424)

lemma oc_c30_2425: "oc_sub oc_b30 2425"
  by (oc_eval oc_c30_2425)

lemma oc_c30_2426: "oc_sub oc_b30 2426"
  by (oc_eval oc_c30_2426)

lemma oc_c30_2427: "oc_sub oc_b30 2427"
  by (oc_eval oc_c30_2427)

lemma oc_c30_2428: "oc_sub oc_b30 2428"
  by (oc_eval oc_c30_2428)

lemma oc_c30_2429: "oc_sub oc_b30 2429"
  by (oc_eval oc_c30_2429)

lemma oc_c30_2430: "oc_sub oc_b30 2430"
  by (oc_eval oc_c30_2430)

lemma oc_c30_2431: "oc_sub oc_b30 2431"
  by (oc_eval oc_c30_2431)

lemma upt_c30_151: "[2416..<2432] = [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]"
  by (simp add: upt_rec)

lemma sec_c30_151: "\<forall>j\<in>{16 * 151..<16 * 151 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 151..<16 * 151 + 16}"
  then have "j \<in> set [2416..<2432]" unfolding set_upt by simp
  then have "j \<in> set [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]" unfolding upt_c30_151 .
  then show "oc_sub oc_b30 j" using oc_c30_2416 oc_c30_2417 oc_c30_2418 oc_c30_2419 oc_c30_2420 oc_c30_2421 oc_c30_2422 oc_c30_2423 oc_c30_2424 oc_c30_2425 oc_c30_2426 oc_c30_2427 oc_c30_2428 oc_c30_2429 oc_c30_2430 oc_c30_2431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
