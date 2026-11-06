theory DCX_c30_157
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2512: "dc_sub dc_b30 2512"
  by (dc_eval dc_c30_2512)

lemma dc_c30_2513: "dc_sub dc_b30 2513"
  by (dc_eval dc_c30_2513)

lemma dc_c30_2514: "dc_sub dc_b30 2514"
  by (dc_eval dc_c30_2514)

lemma dc_c30_2515: "dc_sub dc_b30 2515"
  by (dc_eval dc_c30_2515)

lemma dc_c30_2516: "dc_sub dc_b30 2516"
  by (dc_eval dc_c30_2516)

lemma dc_c30_2517: "dc_sub dc_b30 2517"
  by (dc_eval dc_c30_2517)

lemma dc_c30_2518: "dc_sub dc_b30 2518"
  by (dc_eval dc_c30_2518)

lemma dc_c30_2519: "dc_sub dc_b30 2519"
  by (dc_eval dc_c30_2519)

lemma dc_c30_2520: "dc_sub dc_b30 2520"
  by (dc_eval dc_c30_2520)

lemma dc_c30_2521: "dc_sub dc_b30 2521"
  by (dc_eval dc_c30_2521)

lemma dc_c30_2522: "dc_sub dc_b30 2522"
  by (dc_eval dc_c30_2522)

lemma dc_c30_2523: "dc_sub dc_b30 2523"
  by (dc_eval dc_c30_2523)

lemma dc_c30_2524: "dc_sub dc_b30 2524"
  by (dc_eval dc_c30_2524)

lemma dc_c30_2525: "dc_sub dc_b30 2525"
  by (dc_eval dc_c30_2525)

lemma dc_c30_2526: "dc_sub dc_b30 2526"
  by (dc_eval dc_c30_2526)

lemma dc_c30_2527: "dc_sub dc_b30 2527"
  by (dc_eval dc_c30_2527)

lemma upt_c30_157: "[2512..<2528] = [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]"
  by (simp add: upt_rec)

lemma sec_c30_157: "\<forall>j\<in>{16 * 157..<16 * 157 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 157..<16 * 157 + 16}"
  then have "j \<in> set [2512..<2528]" unfolding set_upt by simp
  then have "j \<in> set [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]" unfolding upt_c30_157 .
  then show "dc_sub dc_b30 j" using dc_c30_2512 dc_c30_2513 dc_c30_2514 dc_c30_2515 dc_c30_2516 dc_c30_2517 dc_c30_2518 dc_c30_2519 dc_c30_2520 dc_c30_2521 dc_c30_2522 dc_c30_2523 dc_c30_2524 dc_c30_2525 dc_c30_2526 dc_c30_2527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
