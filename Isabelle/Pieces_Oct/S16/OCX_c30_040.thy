theory OCX_c30_040
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0640: "oc_sub oc_b30 640"
  by (oc_eval oc_c30_0640)

lemma oc_c30_0641: "oc_sub oc_b30 641"
  by (oc_eval oc_c30_0641)

lemma oc_c30_0642: "oc_sub oc_b30 642"
  by (oc_eval oc_c30_0642)

lemma oc_c30_0643: "oc_sub oc_b30 643"
  by (oc_eval oc_c30_0643)

lemma oc_c30_0644: "oc_sub oc_b30 644"
  by (oc_eval oc_c30_0644)

lemma oc_c30_0645: "oc_sub oc_b30 645"
  by (oc_eval oc_c30_0645)

lemma oc_c30_0646: "oc_sub oc_b30 646"
  by (oc_eval oc_c30_0646)

lemma oc_c30_0647: "oc_sub oc_b30 647"
  by (oc_eval oc_c30_0647)

lemma oc_c30_0648: "oc_sub oc_b30 648"
  by (oc_eval oc_c30_0648)

lemma oc_c30_0649: "oc_sub oc_b30 649"
  by (oc_eval oc_c30_0649)

lemma oc_c30_0650: "oc_sub oc_b30 650"
  by (oc_eval oc_c30_0650)

lemma oc_c30_0651: "oc_sub oc_b30 651"
  by (oc_eval oc_c30_0651)

lemma oc_c30_0652: "oc_sub oc_b30 652"
  by (oc_eval oc_c30_0652)

lemma oc_c30_0653: "oc_sub oc_b30 653"
  by (oc_eval oc_c30_0653)

lemma oc_c30_0654: "oc_sub oc_b30 654"
  by (oc_eval oc_c30_0654)

lemma oc_c30_0655: "oc_sub oc_b30 655"
  by (oc_eval oc_c30_0655)

lemma upt_c30_040: "[640..<656] = [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]"
  by (simp add: upt_rec)

lemma sec_c30_040: "\<forall>j\<in>{16 * 40..<16 * 40 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 40..<16 * 40 + 16}"
  then have "j \<in> set [640..<656]" unfolding set_upt by simp
  then have "j \<in> set [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]" unfolding upt_c30_040 .
  then show "oc_sub oc_b30 j" using oc_c30_0640 oc_c30_0641 oc_c30_0642 oc_c30_0643 oc_c30_0644 oc_c30_0645 oc_c30_0646 oc_c30_0647 oc_c30_0648 oc_c30_0649 oc_c30_0650 oc_c30_0651 oc_c30_0652 oc_c30_0653 oc_c30_0654 oc_c30_0655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
