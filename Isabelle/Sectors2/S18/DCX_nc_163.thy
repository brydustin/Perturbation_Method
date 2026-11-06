theory DCX_nc_163
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2608: "dc_sub None 2608"
  by (dc_eval dc_nc_2608)

lemma dc_nc_2609: "dc_sub None 2609"
  by (dc_eval dc_nc_2609)

lemma dc_nc_2610: "dc_sub None 2610"
  by (dc_eval dc_nc_2610)

lemma dc_nc_2611: "dc_sub None 2611"
  by (dc_eval dc_nc_2611)

lemma dc_nc_2612: "dc_sub None 2612"
  by (dc_eval dc_nc_2612)

lemma dc_nc_2613: "dc_sub None 2613"
  by (dc_eval dc_nc_2613)

lemma dc_nc_2614: "dc_sub None 2614"
  by (dc_eval dc_nc_2614)

lemma dc_nc_2615: "dc_sub None 2615"
  by (dc_eval dc_nc_2615)

lemma dc_nc_2616: "dc_sub None 2616"
  by (dc_eval dc_nc_2616)

lemma dc_nc_2617: "dc_sub None 2617"
  by (dc_eval dc_nc_2617)

lemma dc_nc_2618: "dc_sub None 2618"
  by (dc_eval dc_nc_2618)

lemma dc_nc_2619: "dc_sub None 2619"
  by (dc_eval dc_nc_2619)

lemma dc_nc_2620: "dc_sub None 2620"
  by (dc_eval dc_nc_2620)

lemma dc_nc_2621: "dc_sub None 2621"
  by (dc_eval dc_nc_2621)

lemma dc_nc_2622: "dc_sub None 2622"
  by (dc_eval dc_nc_2622)

lemma dc_nc_2623: "dc_sub None 2623"
  by (dc_eval dc_nc_2623)

lemma upt_nc_163: "[2608..<2624] = [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]"
  by (simp add: upt_rec)

lemma sec_nc_163: "\<forall>j\<in>{16 * 163..<16 * 163 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 163..<16 * 163 + 16}"
  then have "j \<in> set [2608..<2624]" unfolding set_upt by simp
  then have "j \<in> set [2608, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623]" unfolding upt_nc_163 .
  then show "dc_sub None j" using dc_nc_2608 dc_nc_2609 dc_nc_2610 dc_nc_2611 dc_nc_2612 dc_nc_2613 dc_nc_2614 dc_nc_2615 dc_nc_2616 dc_nc_2617 dc_nc_2618 dc_nc_2619 dc_nc_2620 dc_nc_2621 dc_nc_2622 dc_nc_2623
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
