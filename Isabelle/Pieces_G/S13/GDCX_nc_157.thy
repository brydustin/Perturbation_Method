theory GDCX_nc_157
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2512: "gdc_sub None 2512"
  by (gdc_eval gdc_nc_2512)

lemma gdc_nc_2513: "gdc_sub None 2513"
  by (gdc_eval gdc_nc_2513)

lemma gdc_nc_2514: "gdc_sub None 2514"
  by (gdc_eval gdc_nc_2514)

lemma gdc_nc_2515: "gdc_sub None 2515"
  by (gdc_eval gdc_nc_2515)

lemma gdc_nc_2516: "gdc_sub None 2516"
  by (gdc_eval gdc_nc_2516)

lemma gdc_nc_2517: "gdc_sub None 2517"
  by (gdc_eval gdc_nc_2517)

lemma gdc_nc_2518: "gdc_sub None 2518"
  by (gdc_eval gdc_nc_2518)

lemma gdc_nc_2519: "gdc_sub None 2519"
  by (gdc_eval gdc_nc_2519)

lemma gdc_nc_2520: "gdc_sub None 2520"
  by (gdc_eval gdc_nc_2520)

lemma gdc_nc_2521: "gdc_sub None 2521"
  by (gdc_eval gdc_nc_2521)

lemma gdc_nc_2522: "gdc_sub None 2522"
  by (gdc_eval gdc_nc_2522)

lemma gdc_nc_2523: "gdc_sub None 2523"
  by (gdc_eval gdc_nc_2523)

lemma gdc_nc_2524: "gdc_sub None 2524"
  by (gdc_eval gdc_nc_2524)

lemma gdc_nc_2525: "gdc_sub None 2525"
  by (gdc_eval gdc_nc_2525)

lemma gdc_nc_2526: "gdc_sub None 2526"
  by (gdc_eval gdc_nc_2526)

lemma gdc_nc_2527: "gdc_sub None 2527"
  by (gdc_eval gdc_nc_2527)

lemma gupt_nc_157: "[2512..<2528] = [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]"
  by (simp add: upt_rec)

lemma gsec_nc_157: "\<forall>j\<in>{16 * 157..<16 * 157 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 157..<16 * 157 + 16}"
  then have "j \<in> set [2512..<2528]" unfolding set_upt by simp
  then have "j \<in> set [2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527]" unfolding gupt_nc_157 .
  then show "gdc_sub None j" using gdc_nc_2512 gdc_nc_2513 gdc_nc_2514 gdc_nc_2515 gdc_nc_2516 gdc_nc_2517 gdc_nc_2518 gdc_nc_2519 gdc_nc_2520 gdc_nc_2521 gdc_nc_2522 gdc_nc_2523 gdc_nc_2524 gdc_nc_2525 gdc_nc_2526 gdc_nc_2527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
