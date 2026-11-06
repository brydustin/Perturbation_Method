theory DCX_nc_040
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0640: "dc_sub None 640"
  by (dc_eval dc_nc_0640)

lemma dc_nc_0641: "dc_sub None 641"
  by (dc_eval dc_nc_0641)

lemma dc_nc_0642: "dc_sub None 642"
  by (dc_eval dc_nc_0642)

lemma dc_nc_0643: "dc_sub None 643"
  by (dc_eval dc_nc_0643)

lemma dc_nc_0644: "dc_sub None 644"
  by (dc_eval dc_nc_0644)

lemma dc_nc_0645: "dc_sub None 645"
  by (dc_eval dc_nc_0645)

lemma dc_nc_0646: "dc_sub None 646"
  by (dc_eval dc_nc_0646)

lemma dc_nc_0647: "dc_sub None 647"
  by (dc_eval dc_nc_0647)

lemma dc_nc_0648: "dc_sub None 648"
  by (dc_eval dc_nc_0648)

lemma dc_nc_0649: "dc_sub None 649"
  by (dc_eval dc_nc_0649)

lemma dc_nc_0650: "dc_sub None 650"
  by (dc_eval dc_nc_0650)

lemma dc_nc_0651: "dc_sub None 651"
  by (dc_eval dc_nc_0651)

lemma dc_nc_0652: "dc_sub None 652"
  by (dc_eval dc_nc_0652)

lemma dc_nc_0653: "dc_sub None 653"
  by (dc_eval dc_nc_0653)

lemma dc_nc_0654: "dc_sub None 654"
  by (dc_eval dc_nc_0654)

lemma dc_nc_0655: "dc_sub None 655"
  by (dc_eval dc_nc_0655)

lemma upt_nc_040: "[640..<656] = [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]"
  by (simp add: upt_rec)

lemma sec_nc_040: "\<forall>j\<in>{16 * 40..<16 * 40 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 40..<16 * 40 + 16}"
  then have "j \<in> set [640..<656]" unfolding set_upt by simp
  then have "j \<in> set [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]" unfolding upt_nc_040 .
  then show "dc_sub None j" using dc_nc_0640 dc_nc_0641 dc_nc_0642 dc_nc_0643 dc_nc_0644 dc_nc_0645 dc_nc_0646 dc_nc_0647 dc_nc_0648 dc_nc_0649 dc_nc_0650 dc_nc_0651 dc_nc_0652 dc_nc_0653 dc_nc_0654 dc_nc_0655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
