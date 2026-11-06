theory GOCX_nc_153
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2448: "goc_sub None 2448"
  by (goc_eval goc_nc_2448)

lemma goc_nc_2449: "goc_sub None 2449"
  by (goc_eval goc_nc_2449)

lemma goc_nc_2450: "goc_sub None 2450"
  by (goc_eval goc_nc_2450)

lemma goc_nc_2451: "goc_sub None 2451"
  by (goc_eval goc_nc_2451)

lemma goc_nc_2452: "goc_sub None 2452"
  by (goc_eval goc_nc_2452)

lemma goc_nc_2453: "goc_sub None 2453"
  by (goc_eval goc_nc_2453)

lemma goc_nc_2454: "goc_sub None 2454"
  by (goc_eval goc_nc_2454)

lemma goc_nc_2455: "goc_sub None 2455"
  by (goc_eval goc_nc_2455)

lemma goc_nc_2456: "goc_sub None 2456"
  by (goc_eval goc_nc_2456)

lemma goc_nc_2457: "goc_sub None 2457"
  by (goc_eval goc_nc_2457)

lemma goc_nc_2458: "goc_sub None 2458"
  by (goc_eval goc_nc_2458)

lemma goc_nc_2459: "goc_sub None 2459"
  by (goc_eval goc_nc_2459)

lemma goc_nc_2460: "goc_sub None 2460"
  by (goc_eval goc_nc_2460)

lemma goc_nc_2461: "goc_sub None 2461"
  by (goc_eval goc_nc_2461)

lemma goc_nc_2462: "goc_sub None 2462"
  by (goc_eval goc_nc_2462)

lemma goc_nc_2463: "goc_sub None 2463"
  by (goc_eval goc_nc_2463)

lemma gupt_nc_153: "[2448..<2464] = [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]"
  by (simp add: upt_rec)

lemma gsec_nc_153: "\<forall>j\<in>{16 * 153..<16 * 153 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 153..<16 * 153 + 16}"
  then have "j \<in> set [2448..<2464]" unfolding set_upt by simp
  then have "j \<in> set [2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463]" unfolding gupt_nc_153 .
  then show "goc_sub None j" using goc_nc_2448 goc_nc_2449 goc_nc_2450 goc_nc_2451 goc_nc_2452 goc_nc_2453 goc_nc_2454 goc_nc_2455 goc_nc_2456 goc_nc_2457 goc_nc_2458 goc_nc_2459 goc_nc_2460 goc_nc_2461 goc_nc_2462 goc_nc_2463
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
