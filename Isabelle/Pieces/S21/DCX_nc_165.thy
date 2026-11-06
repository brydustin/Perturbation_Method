theory DCX_nc_165
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2640: "dc_sub None 2640"
  by (dc_eval dc_nc_2640)

lemma dc_nc_2641: "dc_sub None 2641"
  by (dc_eval dc_nc_2641)

lemma dc_nc_2642: "dc_sub None 2642"
  by (dc_eval dc_nc_2642)

lemma dc_nc_2643: "dc_sub None 2643"
  by (dc_eval dc_nc_2643)

lemma dc_nc_2644: "dc_sub None 2644"
  by (dc_eval dc_nc_2644)

lemma dc_nc_2645: "dc_sub None 2645"
  by (dc_eval dc_nc_2645)

lemma dc_nc_2646: "dc_sub None 2646"
  by (dc_eval dc_nc_2646)

lemma dc_nc_2647: "dc_sub None 2647"
  by (dc_eval dc_nc_2647)

lemma dc_nc_2648: "dc_sub None 2648"
  by (dc_eval dc_nc_2648)

lemma dc_nc_2649: "dc_sub None 2649"
  by (dc_eval dc_nc_2649)

lemma dc_nc_2650: "dc_sub None 2650"
  by (dc_eval dc_nc_2650)

lemma dc_nc_2651: "dc_sub None 2651"
  by (dc_eval dc_nc_2651)

lemma dc_nc_2652: "dc_sub None 2652"
  by (dc_eval dc_nc_2652)

lemma dc_nc_2653: "dc_sub None 2653"
  by (dc_eval dc_nc_2653)

lemma dc_nc_2654: "dc_sub None 2654"
  by (dc_eval dc_nc_2654)

lemma dc_nc_2655: "dc_sub None 2655"
  by (dc_eval dc_nc_2655)

lemma upt_nc_165: "[2640..<2656] = [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]"
  by (simp add: upt_rec)

lemma sec_nc_165: "\<forall>j\<in>{16 * 165..<16 * 165 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 165..<16 * 165 + 16}"
  then have "j \<in> set [2640..<2656]" unfolding set_upt by simp
  then have "j \<in> set [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]" unfolding upt_nc_165 .
  then show "dc_sub None j" using dc_nc_2640 dc_nc_2641 dc_nc_2642 dc_nc_2643 dc_nc_2644 dc_nc_2645 dc_nc_2646 dc_nc_2647 dc_nc_2648 dc_nc_2649 dc_nc_2650 dc_nc_2651 dc_nc_2652 dc_nc_2653 dc_nc_2654 dc_nc_2655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
