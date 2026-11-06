theory GOCX_nc_157
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2512: "goc_sub None 2512"
  by (goc_eval goc_nc_2512)

lemma goc_nc_2513: "goc_sub None 2513"
  by (goc_eval goc_nc_2513)

lemma goc_nc_2514: "goc_sub None 2514"
  by (goc_eval goc_nc_2514)

lemma goc_nc_2515: "goc_sub None 2515"
  by (goc_eval goc_nc_2515)

lemma goc_nc_2516: "goc_sub None 2516"
  by (goc_eval goc_nc_2516)

lemma goc_nc_2517: "goc_sub None 2517"
  by (goc_eval goc_nc_2517)

lemma goc_nc_2518: "goc_sub None 2518"
  by (goc_eval goc_nc_2518)

lemma goc_nc_2519: "goc_sub None 2519"
  by (goc_eval goc_nc_2519)

lemma goc_nc_2520: "goc_sub None 2520"
  by (goc_eval goc_nc_2520)

lemma goc_nc_2521: "goc_sub None 2521"
  by (goc_eval goc_nc_2521)

lemma goc_nc_2522: "goc_sub None 2522"
  by (goc_eval goc_nc_2522)

lemma goc_nc_2523: "goc_sub None 2523"
  by (goc_eval goc_nc_2523)

lemma goc_nc_2524: "goc_sub None 2524"
  by (goc_eval goc_nc_2524)

lemma goc_nc_2525: "goc_sub None 2525"
  by (goc_eval goc_nc_2525)

lemma goc_nc_2526: "goc_sub None 2526"
  by (goc_eval goc_nc_2526)

lemma goc_nc_2527: "goc_sub None 2527"
  by (goc_eval goc_nc_2527)

lemma gupt_nc_157: "[2512..<2528] = [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]"
  by (simp add: upt_rec)

lemma gsec_nc_157: "\<forall>j\<in>{16 * 157..<16 * 157 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 157..<16 * 157 + 16}"
  then have "j \<in> set [2512..<2528]" unfolding set_upt by simp
  then have "j \<in> set [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]" unfolding gupt_nc_157 .
  then show "goc_sub None j" using goc_nc_2512 goc_nc_2513 goc_nc_2514 goc_nc_2515 goc_nc_2516 goc_nc_2517 goc_nc_2518 goc_nc_2519 goc_nc_2520 goc_nc_2521 goc_nc_2522 goc_nc_2523 goc_nc_2524 goc_nc_2525 goc_nc_2526 goc_nc_2527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
