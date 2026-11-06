theory DCX_nc_157
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2512: "dc_sub None 2512"
  by (dc_eval dc_nc_2512)

lemma dc_nc_2513: "dc_sub None 2513"
  by (dc_eval dc_nc_2513)

lemma dc_nc_2514: "dc_sub None 2514"
  by (dc_eval dc_nc_2514)

lemma dc_nc_2515: "dc_sub None 2515"
  by (dc_eval dc_nc_2515)

lemma dc_nc_2516: "dc_sub None 2516"
  by (dc_eval dc_nc_2516)

lemma dc_nc_2517: "dc_sub None 2517"
  by (dc_eval dc_nc_2517)

lemma dc_nc_2518: "dc_sub None 2518"
  by (dc_eval dc_nc_2518)

lemma dc_nc_2519: "dc_sub None 2519"
  by (dc_eval dc_nc_2519)

lemma dc_nc_2520: "dc_sub None 2520"
  by (dc_eval dc_nc_2520)

lemma dc_nc_2521: "dc_sub None 2521"
  by (dc_eval dc_nc_2521)

lemma dc_nc_2522: "dc_sub None 2522"
  by (dc_eval dc_nc_2522)

lemma dc_nc_2523: "dc_sub None 2523"
  by (dc_eval dc_nc_2523)

lemma dc_nc_2524: "dc_sub None 2524"
  by (dc_eval dc_nc_2524)

lemma dc_nc_2525: "dc_sub None 2525"
  by (dc_eval dc_nc_2525)

lemma dc_nc_2526: "dc_sub None 2526"
  by (dc_eval dc_nc_2526)

lemma dc_nc_2527: "dc_sub None 2527"
  by (dc_eval dc_nc_2527)

lemma upt_nc_157: "[2512..<2528] = [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]"
  by (simp add: upt_rec)

lemma sec_nc_157: "\<forall>j\<in>{16 * 157..<16 * 157 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 157..<16 * 157 + 16}"
  then have "j \<in> set [2512..<2528]" unfolding set_upt by simp
  then have "j \<in> set [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]" unfolding upt_nc_157 .
  then show "dc_sub None j" using dc_nc_2512 dc_nc_2513 dc_nc_2514 dc_nc_2515 dc_nc_2516 dc_nc_2517 dc_nc_2518 dc_nc_2519 dc_nc_2520 dc_nc_2521 dc_nc_2522 dc_nc_2523 dc_nc_2524 dc_nc_2525 dc_nc_2526 dc_nc_2527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
