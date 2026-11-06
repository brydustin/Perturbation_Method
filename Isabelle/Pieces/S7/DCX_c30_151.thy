theory DCX_c30_151
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2416: "dc_sub dc_b30 2416"
  by (dc_eval dc_c30_2416)

lemma dc_c30_2417: "dc_sub dc_b30 2417"
  by (dc_eval dc_c30_2417)

lemma dc_c30_2418: "dc_sub dc_b30 2418"
  by (dc_eval dc_c30_2418)

lemma dc_c30_2419: "dc_sub dc_b30 2419"
  by (dc_eval dc_c30_2419)

lemma dc_c30_2420: "dc_sub dc_b30 2420"
  by (dc_eval dc_c30_2420)

lemma dc_c30_2421: "dc_sub dc_b30 2421"
  by (dc_eval dc_c30_2421)

lemma dc_c30_2422: "dc_sub dc_b30 2422"
  by (dc_eval dc_c30_2422)

lemma dc_c30_2423: "dc_sub dc_b30 2423"
  by (dc_eval dc_c30_2423)

lemma dc_c30_2424: "dc_sub dc_b30 2424"
  by (dc_eval dc_c30_2424)

lemma dc_c30_2425: "dc_sub dc_b30 2425"
  by (dc_eval dc_c30_2425)

lemma dc_c30_2426: "dc_sub dc_b30 2426"
  by (dc_eval dc_c30_2426)

lemma dc_c30_2427: "dc_sub dc_b30 2427"
  by (dc_eval dc_c30_2427)

lemma dc_c30_2428: "dc_sub dc_b30 2428"
  by (dc_eval dc_c30_2428)

lemma dc_c30_2429: "dc_sub dc_b30 2429"
  by (dc_eval dc_c30_2429)

lemma dc_c30_2430: "dc_sub dc_b30 2430"
  by (dc_eval dc_c30_2430)

lemma dc_c30_2431: "dc_sub dc_b30 2431"
  by (dc_eval dc_c30_2431)

lemma upt_c30_151: "[2416..<2432] = [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]"
  by (simp add: upt_rec)

lemma sec_c30_151: "\<forall>j\<in>{16 * 151..<16 * 151 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 151..<16 * 151 + 16}"
  then have "j \<in> set [2416..<2432]" unfolding set_upt by simp
  then have "j \<in> set [2416, 2417, 2418, 2419, 2420, 2421, 2422, 2423, 2424, 2425, 2426, 2427, 2428, 2429, 2430, 2431]" unfolding upt_c30_151 .
  then show "dc_sub dc_b30 j" using dc_c30_2416 dc_c30_2417 dc_c30_2418 dc_c30_2419 dc_c30_2420 dc_c30_2421 dc_c30_2422 dc_c30_2423 dc_c30_2424 dc_c30_2425 dc_c30_2426 dc_c30_2427 dc_c30_2428 dc_c30_2429 dc_c30_2430 dc_c30_2431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
