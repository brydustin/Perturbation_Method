theory GOCX_nc_163
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2608: "goc_sub None 2608"
  by (goc_eval goc_nc_2608)

lemma goc_nc_2609: "goc_sub None 2609"
  by (goc_eval goc_nc_2609)

lemma goc_nc_2610: "goc_sub None 2610"
  by (goc_eval goc_nc_2610)

lemma goc_nc_2611: "goc_sub None 2611"
  by (goc_eval goc_nc_2611)

lemma goc_nc_2612: "goc_sub None 2612"
  by (goc_eval goc_nc_2612)

lemma goc_nc_2613: "goc_sub None 2613"
  by (goc_eval goc_nc_2613)

lemma goc_nc_2614: "goc_sub None 2614"
  by (goc_eval goc_nc_2614)

lemma goc_nc_2615: "goc_sub None 2615"
  by (goc_eval goc_nc_2615)

lemma goc_nc_2616: "goc_sub None 2616"
  by (goc_eval goc_nc_2616)

lemma goc_nc_2617: "goc_sub None 2617"
  by (goc_eval goc_nc_2617)

lemma goc_nc_2618: "goc_sub None 2618"
  by (goc_eval goc_nc_2618)

lemma goc_nc_2619: "goc_sub None 2619"
  by (goc_eval goc_nc_2619)

lemma goc_nc_2620: "goc_sub None 2620"
  by (goc_eval goc_nc_2620)

lemma goc_nc_2621: "goc_sub None 2621"
  by (goc_eval goc_nc_2621)

lemma goc_nc_2622: "goc_sub None 2622"
  by (goc_eval goc_nc_2622)

lemma goc_nc_2623: "goc_sub None 2623"
  by (goc_eval goc_nc_2623)

lemma gupt_nc_163: "[2608..<2624] = [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]"
  by (simp add: upt_rec)

lemma gsec_nc_163: "\<forall>j\<in>{16 * 163..<16 * 163 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 163..<16 * 163 + 16}"
  then have "j \<in> set [2608..<2624]" unfolding set_upt by simp
  then have "j \<in> set [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]" unfolding gupt_nc_163 .
  then show "goc_sub None j" using goc_nc_2608 goc_nc_2609 goc_nc_2610 goc_nc_2611 goc_nc_2612 goc_nc_2613 goc_nc_2614 goc_nc_2615 goc_nc_2616 goc_nc_2617 goc_nc_2618 goc_nc_2619 goc_nc_2620 goc_nc_2621 goc_nc_2622 goc_nc_2623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
