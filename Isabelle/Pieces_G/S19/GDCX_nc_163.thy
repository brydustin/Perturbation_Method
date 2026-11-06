theory GDCX_nc_163
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2608: "gdc_sub None 2608"
  by (gdc_eval gdc_nc_2608)

lemma gdc_nc_2609: "gdc_sub None 2609"
  by (gdc_eval gdc_nc_2609)

lemma gdc_nc_2610: "gdc_sub None 2610"
  by (gdc_eval gdc_nc_2610)

lemma gdc_nc_2611: "gdc_sub None 2611"
  by (gdc_eval gdc_nc_2611)

lemma gdc_nc_2612: "gdc_sub None 2612"
  by (gdc_eval gdc_nc_2612)

lemma gdc_nc_2613: "gdc_sub None 2613"
  by (gdc_eval gdc_nc_2613)

lemma gdc_nc_2614: "gdc_sub None 2614"
  by (gdc_eval gdc_nc_2614)

lemma gdc_nc_2615: "gdc_sub None 2615"
  by (gdc_eval gdc_nc_2615)

lemma gdc_nc_2616: "gdc_sub None 2616"
  by (gdc_eval gdc_nc_2616)

lemma gdc_nc_2617: "gdc_sub None 2617"
  by (gdc_eval gdc_nc_2617)

lemma gdc_nc_2618: "gdc_sub None 2618"
  by (gdc_eval gdc_nc_2618)

lemma gdc_nc_2619: "gdc_sub None 2619"
  by (gdc_eval gdc_nc_2619)

lemma gdc_nc_2620: "gdc_sub None 2620"
  by (gdc_eval gdc_nc_2620)

lemma gdc_nc_2621: "gdc_sub None 2621"
  by (gdc_eval gdc_nc_2621)

lemma gdc_nc_2622: "gdc_sub None 2622"
  by (gdc_eval gdc_nc_2622)

lemma gdc_nc_2623: "gdc_sub None 2623"
  by (gdc_eval gdc_nc_2623)

lemma gupt_nc_163: "[2608..<2624] = [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]"
  by (simp add: upt_rec)

lemma gsec_nc_163: "\<forall>j\<in>{16 * 163..<16 * 163 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 163..<16 * 163 + 16}"
  then have "j \<in> set [2608..<2624]" unfolding set_upt by simp
  then have "j \<in> set [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]" unfolding gupt_nc_163 .
  then show "gdc_sub None j" using gdc_nc_2608 gdc_nc_2609 gdc_nc_2610 gdc_nc_2611 gdc_nc_2612 gdc_nc_2613 gdc_nc_2614 gdc_nc_2615 gdc_nc_2616 gdc_nc_2617 gdc_nc_2618 gdc_nc_2619 gdc_nc_2620 gdc_nc_2621 gdc_nc_2622 gdc_nc_2623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
