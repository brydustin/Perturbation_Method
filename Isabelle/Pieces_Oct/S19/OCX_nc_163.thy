theory OCX_nc_163
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2608: "oc_sub None 2608"
  by (oc_eval oc_nc_2608)

lemma oc_nc_2609: "oc_sub None 2609"
  by (oc_eval oc_nc_2609)

lemma oc_nc_2610: "oc_sub None 2610"
  by (oc_eval oc_nc_2610)

lemma oc_nc_2611: "oc_sub None 2611"
  by (oc_eval oc_nc_2611)

lemma oc_nc_2612: "oc_sub None 2612"
  by (oc_eval oc_nc_2612)

lemma oc_nc_2613: "oc_sub None 2613"
  by (oc_eval oc_nc_2613)

lemma oc_nc_2614: "oc_sub None 2614"
  by (oc_eval oc_nc_2614)

lemma oc_nc_2615: "oc_sub None 2615"
  by (oc_eval oc_nc_2615)

lemma oc_nc_2616: "oc_sub None 2616"
  by (oc_eval oc_nc_2616)

lemma oc_nc_2617: "oc_sub None 2617"
  by (oc_eval oc_nc_2617)

lemma oc_nc_2618: "oc_sub None 2618"
  by (oc_eval oc_nc_2618)

lemma oc_nc_2619: "oc_sub None 2619"
  by (oc_eval oc_nc_2619)

lemma oc_nc_2620: "oc_sub None 2620"
  by (oc_eval oc_nc_2620)

lemma oc_nc_2621: "oc_sub None 2621"
  by (oc_eval oc_nc_2621)

lemma oc_nc_2622: "oc_sub None 2622"
  by (oc_eval oc_nc_2622)

lemma oc_nc_2623: "oc_sub None 2623"
  by (oc_eval oc_nc_2623)

lemma upt_nc_163: "[2608..<2624] = [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]"
  by (simp add: upt_rec)

lemma sec_nc_163: "\<forall>j\<in>{16 * 163..<16 * 163 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 163..<16 * 163 + 16}"
  then have "j \<in> set [2608..<2624]" unfolding set_upt by simp
  then have "j \<in> set [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]" unfolding upt_nc_163 .
  then show "oc_sub None j" using oc_nc_2608 oc_nc_2609 oc_nc_2610 oc_nc_2611 oc_nc_2612 oc_nc_2613 oc_nc_2614 oc_nc_2615 oc_nc_2616 oc_nc_2617 oc_nc_2618 oc_nc_2619 oc_nc_2620 oc_nc_2621 oc_nc_2622 oc_nc_2623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
