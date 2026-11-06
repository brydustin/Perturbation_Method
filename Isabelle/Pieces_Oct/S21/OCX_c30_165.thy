theory OCX_c30_165
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2640: "oc_sub oc_b30 2640"
  by (oc_eval oc_c30_2640)

lemma oc_c30_2641: "oc_sub oc_b30 2641"
  by (oc_eval oc_c30_2641)

lemma oc_c30_2642: "oc_sub oc_b30 2642"
  by (oc_eval oc_c30_2642)

lemma oc_c30_2643: "oc_sub oc_b30 2643"
  by (oc_eval oc_c30_2643)

lemma oc_c30_2644: "oc_sub oc_b30 2644"
  by (oc_eval oc_c30_2644)

lemma oc_c30_2645: "oc_sub oc_b30 2645"
  by (oc_eval oc_c30_2645)

lemma oc_c30_2646: "oc_sub oc_b30 2646"
  by (oc_eval oc_c30_2646)

lemma oc_c30_2647: "oc_sub oc_b30 2647"
  by (oc_eval oc_c30_2647)

lemma oc_c30_2648: "oc_sub oc_b30 2648"
  by (oc_eval oc_c30_2648)

lemma oc_c30_2649: "oc_sub oc_b30 2649"
  by (oc_eval oc_c30_2649)

lemma oc_c30_2650: "oc_sub oc_b30 2650"
  by (oc_eval oc_c30_2650)

lemma oc_c30_2651: "oc_sub oc_b30 2651"
  by (oc_eval oc_c30_2651)

lemma oc_c30_2652: "oc_sub oc_b30 2652"
  by (oc_eval oc_c30_2652)

lemma oc_c30_2653: "oc_sub oc_b30 2653"
  by (oc_eval oc_c30_2653)

lemma oc_c30_2654: "oc_sub oc_b30 2654"
  by (oc_eval oc_c30_2654)

lemma oc_c30_2655: "oc_sub oc_b30 2655"
  by (oc_eval oc_c30_2655)

lemma upt_c30_165: "[2640..<2656] = [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]"
  by (simp add: upt_rec)

lemma sec_c30_165: "\<forall>j\<in>{16 * 165..<16 * 165 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 165..<16 * 165 + 16}"
  then have "j \<in> set [2640..<2656]" unfolding set_upt by simp
  then have "j \<in> set [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]" unfolding upt_c30_165 .
  then show "oc_sub oc_b30 j" using oc_c30_2640 oc_c30_2641 oc_c30_2642 oc_c30_2643 oc_c30_2644 oc_c30_2645 oc_c30_2646 oc_c30_2647 oc_c30_2648 oc_c30_2649 oc_c30_2650 oc_c30_2651 oc_c30_2652 oc_c30_2653 oc_c30_2654 oc_c30_2655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
