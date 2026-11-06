theory OCX_nc_151
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2416: "oc_sub None 2416"
  by (oc_eval oc_nc_2416)

lemma oc_nc_2417: "oc_sub None 2417"
  by (oc_eval oc_nc_2417)

lemma oc_nc_2418: "oc_sub None 2418"
  by (oc_eval oc_nc_2418)

lemma oc_nc_2419: "oc_sub None 2419"
  by (oc_eval oc_nc_2419)

lemma oc_nc_2420: "oc_sub None 2420"
  by (oc_eval oc_nc_2420)

lemma oc_nc_2421: "oc_sub None 2421"
  by (oc_eval oc_nc_2421)

lemma oc_nc_2422: "oc_sub None 2422"
  by (oc_eval oc_nc_2422)

lemma oc_nc_2423: "oc_sub None 2423"
  by (oc_eval oc_nc_2423)

lemma oc_nc_2424: "oc_sub None 2424"
  by (oc_eval oc_nc_2424)

lemma oc_nc_2425: "oc_sub None 2425"
  by (oc_eval oc_nc_2425)

lemma oc_nc_2426: "oc_sub None 2426"
  by (oc_eval oc_nc_2426)

lemma oc_nc_2427: "oc_sub None 2427"
  by (oc_eval oc_nc_2427)

lemma oc_nc_2428: "oc_sub None 2428"
  by (oc_eval oc_nc_2428)

lemma oc_nc_2429: "oc_sub None 2429"
  by (oc_eval oc_nc_2429)

lemma oc_nc_2430: "oc_sub None 2430"
  by (oc_eval oc_nc_2430)

lemma oc_nc_2431: "oc_sub None 2431"
  by (oc_eval oc_nc_2431)

lemma upt_nc_151: "[2416..<2432] = [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]"
  by (simp add: upt_rec)

lemma sec_nc_151: "\<forall>j\<in>{16 * 151..<16 * 151 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 151..<16 * 151 + 16}"
  then have "j \<in> set [2416..<2432]" unfolding set_upt by simp
  then have "j \<in> set [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]" unfolding upt_nc_151 .
  then show "oc_sub None j" using oc_nc_2416 oc_nc_2417 oc_nc_2418 oc_nc_2419 oc_nc_2420 oc_nc_2421 oc_nc_2422 oc_nc_2423 oc_nc_2424 oc_nc_2425 oc_nc_2426 oc_nc_2427 oc_nc_2428 oc_nc_2429 oc_nc_2430 oc_nc_2431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
