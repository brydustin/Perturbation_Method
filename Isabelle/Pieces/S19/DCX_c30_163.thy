theory DCX_c30_163
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2608: "dc_sub dc_b30 2608"
  by (dc_eval dc_c30_2608)

lemma dc_c30_2609: "dc_sub dc_b30 2609"
  by (dc_eval dc_c30_2609)

lemma dc_c30_2610: "dc_sub dc_b30 2610"
  by (dc_eval dc_c30_2610)

lemma dc_c30_2611: "dc_sub dc_b30 2611"
  by (dc_eval dc_c30_2611)

lemma dc_c30_2612: "dc_sub dc_b30 2612"
  by (dc_eval dc_c30_2612)

lemma dc_c30_2613: "dc_sub dc_b30 2613"
  by (dc_eval dc_c30_2613)

lemma dc_c30_2614: "dc_sub dc_b30 2614"
  by (dc_eval dc_c30_2614)

lemma dc_c30_2615: "dc_sub dc_b30 2615"
  by (dc_eval dc_c30_2615)

lemma dc_c30_2616: "dc_sub dc_b30 2616"
  by (dc_eval dc_c30_2616)

lemma dc_c30_2617: "dc_sub dc_b30 2617"
  by (dc_eval dc_c30_2617)

lemma dc_c30_2618: "dc_sub dc_b30 2618"
  by (dc_eval dc_c30_2618)

lemma dc_c30_2619: "dc_sub dc_b30 2619"
  by (dc_eval dc_c30_2619)

lemma dc_c30_2620: "dc_sub dc_b30 2620"
  by (dc_eval dc_c30_2620)

lemma dc_c30_2621: "dc_sub dc_b30 2621"
  by (dc_eval dc_c30_2621)

lemma dc_c30_2622: "dc_sub dc_b30 2622"
  by (dc_eval dc_c30_2622)

lemma dc_c30_2623: "dc_sub dc_b30 2623"
  by (dc_eval dc_c30_2623)

lemma upt_c30_163: "[2608..<2624] = [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]"
  by (simp add: upt_rec)

lemma sec_c30_163: "\<forall>j\<in>{16 * 163..<16 * 163 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 163..<16 * 163 + 16}"
  then have "j \<in> set [2608..<2624]" unfolding set_upt by simp
  then have "j \<in> set [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]" unfolding upt_c30_163 .
  then show "dc_sub dc_b30 j" using dc_c30_2608 dc_c30_2609 dc_c30_2610 dc_c30_2611 dc_c30_2612 dc_c30_2613 dc_c30_2614 dc_c30_2615 dc_c30_2616 dc_c30_2617 dc_c30_2618 dc_c30_2619 dc_c30_2620 dc_c30_2621 dc_c30_2622 dc_c30_2623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
