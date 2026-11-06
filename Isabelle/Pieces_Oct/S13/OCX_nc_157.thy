theory OCX_nc_157
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2512: "oc_sub None 2512"
  by (oc_eval oc_nc_2512)

lemma oc_nc_2513: "oc_sub None 2513"
  by (oc_eval oc_nc_2513)

lemma oc_nc_2514: "oc_sub None 2514"
  by (oc_eval oc_nc_2514)

lemma oc_nc_2515: "oc_sub None 2515"
  by (oc_eval oc_nc_2515)

lemma oc_nc_2516: "oc_sub None 2516"
  by (oc_eval oc_nc_2516)

lemma oc_nc_2517: "oc_sub None 2517"
  by (oc_eval oc_nc_2517)

lemma oc_nc_2518: "oc_sub None 2518"
  by (oc_eval oc_nc_2518)

lemma oc_nc_2519: "oc_sub None 2519"
  by (oc_eval oc_nc_2519)

lemma oc_nc_2520: "oc_sub None 2520"
  by (oc_eval oc_nc_2520)

lemma oc_nc_2521: "oc_sub None 2521"
  by (oc_eval oc_nc_2521)

lemma oc_nc_2522: "oc_sub None 2522"
  by (oc_eval oc_nc_2522)

lemma oc_nc_2523: "oc_sub None 2523"
  by (oc_eval oc_nc_2523)

lemma oc_nc_2524: "oc_sub None 2524"
  by (oc_eval oc_nc_2524)

lemma oc_nc_2525: "oc_sub None 2525"
  by (oc_eval oc_nc_2525)

lemma oc_nc_2526: "oc_sub None 2526"
  by (oc_eval oc_nc_2526)

lemma oc_nc_2527: "oc_sub None 2527"
  by (oc_eval oc_nc_2527)

lemma upt_nc_157: "[2512..<2528] = [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]"
  by (simp add: upt_rec)

lemma sec_nc_157: "\<forall>j\<in>{16 * 157..<16 * 157 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 157..<16 * 157 + 16}"
  then have "j \<in> set [2512..<2528]" unfolding set_upt by simp
  then have "j \<in> set [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]" unfolding upt_nc_157 .
  then show "oc_sub None j" using oc_nc_2512 oc_nc_2513 oc_nc_2514 oc_nc_2515 oc_nc_2516 oc_nc_2517 oc_nc_2518 oc_nc_2519 oc_nc_2520 oc_nc_2521 oc_nc_2522 oc_nc_2523 oc_nc_2524 oc_nc_2525 oc_nc_2526 oc_nc_2527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
