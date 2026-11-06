theory GDCX_nc_153
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2448: "gdc_sub None 2448"
  by (gdc_eval gdc_nc_2448)

lemma gdc_nc_2449: "gdc_sub None 2449"
  by (gdc_eval gdc_nc_2449)

lemma gdc_nc_2450: "gdc_sub None 2450"
  by (gdc_eval gdc_nc_2450)

lemma gdc_nc_2451: "gdc_sub None 2451"
  by (gdc_eval gdc_nc_2451)

lemma gdc_nc_2452: "gdc_sub None 2452"
  by (gdc_eval gdc_nc_2452)

lemma gdc_nc_2453: "gdc_sub None 2453"
  by (gdc_eval gdc_nc_2453)

lemma gdc_nc_2454: "gdc_sub None 2454"
  by (gdc_eval gdc_nc_2454)

lemma gdc_nc_2455: "gdc_sub None 2455"
  by (gdc_eval gdc_nc_2455)

lemma gdc_nc_2456: "gdc_sub None 2456"
  by (gdc_eval gdc_nc_2456)

lemma gdc_nc_2457: "gdc_sub None 2457"
  by (gdc_eval gdc_nc_2457)

lemma gdc_nc_2458: "gdc_sub None 2458"
  by (gdc_eval gdc_nc_2458)

lemma gdc_nc_2459: "gdc_sub None 2459"
  by (gdc_eval gdc_nc_2459)

lemma gdc_nc_2460: "gdc_sub None 2460"
  by (gdc_eval gdc_nc_2460)

lemma gdc_nc_2461: "gdc_sub None 2461"
  by (gdc_eval gdc_nc_2461)

lemma gdc_nc_2462: "gdc_sub None 2462"
  by (gdc_eval gdc_nc_2462)

lemma gdc_nc_2463: "gdc_sub None 2463"
  by (gdc_eval gdc_nc_2463)

lemma gupt_nc_153: "[2448..<2464] = [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]"
  by (simp add: upt_rec)

lemma gsec_nc_153: "\<forall>j\<in>{16 * 153..<16 * 153 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 153..<16 * 153 + 16}"
  then have "j \<in> set [2448..<2464]" unfolding set_upt by simp
  then have "j \<in> set [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]" unfolding gupt_nc_153 .
  then show "gdc_sub None j" using gdc_nc_2448 gdc_nc_2449 gdc_nc_2450 gdc_nc_2451 gdc_nc_2452 gdc_nc_2453 gdc_nc_2454 gdc_nc_2455 gdc_nc_2456 gdc_nc_2457 gdc_nc_2458 gdc_nc_2459 gdc_nc_2460 gdc_nc_2461 gdc_nc_2462 gdc_nc_2463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
