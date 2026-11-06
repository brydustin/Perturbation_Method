theory OCX_nc_040
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0640: "oc_sub None 640"
  by (oc_eval oc_nc_0640)

lemma oc_nc_0641: "oc_sub None 641"
  by (oc_eval oc_nc_0641)

lemma oc_nc_0642: "oc_sub None 642"
  by (oc_eval oc_nc_0642)

lemma oc_nc_0643: "oc_sub None 643"
  by (oc_eval oc_nc_0643)

lemma oc_nc_0644: "oc_sub None 644"
  by (oc_eval oc_nc_0644)

lemma oc_nc_0645: "oc_sub None 645"
  by (oc_eval oc_nc_0645)

lemma oc_nc_0646: "oc_sub None 646"
  by (oc_eval oc_nc_0646)

lemma oc_nc_0647: "oc_sub None 647"
  by (oc_eval oc_nc_0647)

lemma oc_nc_0648: "oc_sub None 648"
  by (oc_eval oc_nc_0648)

lemma oc_nc_0649: "oc_sub None 649"
  by (oc_eval oc_nc_0649)

lemma oc_nc_0650: "oc_sub None 650"
  by (oc_eval oc_nc_0650)

lemma oc_nc_0651: "oc_sub None 651"
  by (oc_eval oc_nc_0651)

lemma oc_nc_0652: "oc_sub None 652"
  by (oc_eval oc_nc_0652)

lemma oc_nc_0653: "oc_sub None 653"
  by (oc_eval oc_nc_0653)

lemma oc_nc_0654: "oc_sub None 654"
  by (oc_eval oc_nc_0654)

lemma oc_nc_0655: "oc_sub None 655"
  by (oc_eval oc_nc_0655)

lemma upt_nc_040: "[640..<656] = [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]"
  by (simp add: upt_rec)

lemma sec_nc_040: "\<forall>j\<in>{16 * 40..<16 * 40 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 40..<16 * 40 + 16}"
  then have "j \<in> set [640..<656]" unfolding set_upt by simp
  then have "j \<in> set [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]" unfolding upt_nc_040 .
  then show "oc_sub None j" using oc_nc_0640 oc_nc_0641 oc_nc_0642 oc_nc_0643 oc_nc_0644 oc_nc_0645 oc_nc_0646 oc_nc_0647 oc_nc_0648 oc_nc_0649 oc_nc_0650 oc_nc_0651 oc_nc_0652 oc_nc_0653 oc_nc_0654 oc_nc_0655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
