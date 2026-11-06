theory DCX_c30_165
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2640: "dc_sub dc_b30 2640"
  by (dc_eval dc_c30_2640)

lemma dc_c30_2641: "dc_sub dc_b30 2641"
  by (dc_eval dc_c30_2641)

lemma dc_c30_2642: "dc_sub dc_b30 2642"
  by (dc_eval dc_c30_2642)

lemma dc_c30_2643: "dc_sub dc_b30 2643"
  by (dc_eval dc_c30_2643)

lemma dc_c30_2644: "dc_sub dc_b30 2644"
  by (dc_eval dc_c30_2644)

lemma dc_c30_2645: "dc_sub dc_b30 2645"
  by (dc_eval dc_c30_2645)

lemma dc_c30_2646: "dc_sub dc_b30 2646"
  by (dc_eval dc_c30_2646)

lemma dc_c30_2647: "dc_sub dc_b30 2647"
  by (dc_eval dc_c30_2647)

lemma dc_c30_2648: "dc_sub dc_b30 2648"
  by (dc_eval dc_c30_2648)

lemma dc_c30_2649: "dc_sub dc_b30 2649"
  by (dc_eval dc_c30_2649)

lemma dc_c30_2650: "dc_sub dc_b30 2650"
  by (dc_eval dc_c30_2650)

lemma dc_c30_2651: "dc_sub dc_b30 2651"
  by (dc_eval dc_c30_2651)

lemma dc_c30_2652: "dc_sub dc_b30 2652"
  by (dc_eval dc_c30_2652)

lemma dc_c30_2653: "dc_sub dc_b30 2653"
  by (dc_eval dc_c30_2653)

lemma dc_c30_2654: "dc_sub dc_b30 2654"
  by (dc_eval dc_c30_2654)

lemma dc_c30_2655: "dc_sub dc_b30 2655"
  by (dc_eval dc_c30_2655)

lemma upt_c30_165: "[2640..<2656] = [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]"
  by (simp add: upt_rec)

lemma sec_c30_165: "\<forall>j\<in>{16 * 165..<16 * 165 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 165..<16 * 165 + 16}"
  then have "j \<in> set [2640..<2656]" unfolding set_upt by simp
  then have "j \<in> set [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]" unfolding upt_c30_165 .
  then show "dc_sub dc_b30 j" using dc_c30_2640 dc_c30_2641 dc_c30_2642 dc_c30_2643 dc_c30_2644 dc_c30_2645 dc_c30_2646 dc_c30_2647 dc_c30_2648 dc_c30_2649 dc_c30_2650 dc_c30_2651 dc_c30_2652 dc_c30_2653 dc_c30_2654 dc_c30_2655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
