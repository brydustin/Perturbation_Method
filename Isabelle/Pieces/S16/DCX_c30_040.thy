theory DCX_c30_040
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0640: "dc_sub dc_b30 640"
  by (dc_eval dc_c30_0640)

lemma dc_c30_0641: "dc_sub dc_b30 641"
  by (dc_eval dc_c30_0641)

lemma dc_c30_0642: "dc_sub dc_b30 642"
  by (dc_eval dc_c30_0642)

lemma dc_c30_0643: "dc_sub dc_b30 643"
  by (dc_eval dc_c30_0643)

lemma dc_c30_0644: "dc_sub dc_b30 644"
  by (dc_eval dc_c30_0644)

lemma dc_c30_0645: "dc_sub dc_b30 645"
  by (dc_eval dc_c30_0645)

lemma dc_c30_0646: "dc_sub dc_b30 646"
  by (dc_eval dc_c30_0646)

lemma dc_c30_0647: "dc_sub dc_b30 647"
  by (dc_eval dc_c30_0647)

lemma dc_c30_0648: "dc_sub dc_b30 648"
  by (dc_eval dc_c30_0648)

lemma dc_c30_0649: "dc_sub dc_b30 649"
  by (dc_eval dc_c30_0649)

lemma dc_c30_0650: "dc_sub dc_b30 650"
  by (dc_eval dc_c30_0650)

lemma dc_c30_0651: "dc_sub dc_b30 651"
  by (dc_eval dc_c30_0651)

lemma dc_c30_0652: "dc_sub dc_b30 652"
  by (dc_eval dc_c30_0652)

lemma dc_c30_0653: "dc_sub dc_b30 653"
  by (dc_eval dc_c30_0653)

lemma dc_c30_0654: "dc_sub dc_b30 654"
  by (dc_eval dc_c30_0654)

lemma dc_c30_0655: "dc_sub dc_b30 655"
  by (dc_eval dc_c30_0655)

lemma upt_c30_040: "[640..<656] = [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]"
  by (simp add: upt_rec)

lemma sec_c30_040: "\<forall>j\<in>{16 * 40..<16 * 40 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 40..<16 * 40 + 16}"
  then have "j \<in> set [640..<656]" unfolding set_upt by simp
  then have "j \<in> set [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]" unfolding upt_c30_040 .
  then show "dc_sub dc_b30 j" using dc_c30_0640 dc_c30_0641 dc_c30_0642 dc_c30_0643 dc_c30_0644 dc_c30_0645 dc_c30_0646 dc_c30_0647 dc_c30_0648 dc_c30_0649 dc_c30_0650 dc_c30_0651 dc_c30_0652 dc_c30_0653 dc_c30_0654 dc_c30_0655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
