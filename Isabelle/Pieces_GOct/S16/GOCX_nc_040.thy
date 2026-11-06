theory GOCX_nc_040
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0640: "goc_sub None 640"
  by (goc_eval goc_nc_0640)

lemma goc_nc_0641: "goc_sub None 641"
  by (goc_eval goc_nc_0641)

lemma goc_nc_0642: "goc_sub None 642"
  by (goc_eval goc_nc_0642)

lemma goc_nc_0643: "goc_sub None 643"
  by (goc_eval goc_nc_0643)

lemma goc_nc_0644: "goc_sub None 644"
  by (goc_eval goc_nc_0644)

lemma goc_nc_0645: "goc_sub None 645"
  by (goc_eval goc_nc_0645)

lemma goc_nc_0646: "goc_sub None 646"
  by (goc_eval goc_nc_0646)

lemma goc_nc_0647: "goc_sub None 647"
  by (goc_eval goc_nc_0647)

lemma goc_nc_0648: "goc_sub None 648"
  by (goc_eval goc_nc_0648)

lemma goc_nc_0649: "goc_sub None 649"
  by (goc_eval goc_nc_0649)

lemma goc_nc_0650: "goc_sub None 650"
  by (goc_eval goc_nc_0650)

lemma goc_nc_0651: "goc_sub None 651"
  by (goc_eval goc_nc_0651)

lemma goc_nc_0652: "goc_sub None 652"
  by (goc_eval goc_nc_0652)

lemma goc_nc_0653: "goc_sub None 653"
  by (goc_eval goc_nc_0653)

lemma goc_nc_0654: "goc_sub None 654"
  by (goc_eval goc_nc_0654)

lemma goc_nc_0655: "goc_sub None 655"
  by (goc_eval goc_nc_0655)

lemma gupt_nc_040: "[640..<656] = [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]"
  by (simp add: upt_rec)

lemma gsec_nc_040: "\<forall>j\<in>{16 * 40..<16 * 40 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 40..<16 * 40 + 16}"
  then have "j \<in> set [640..<656]" unfolding set_upt by simp
  then have "j \<in> set [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]" unfolding gupt_nc_040 .
  then show "goc_sub None j" using goc_nc_0640 goc_nc_0641 goc_nc_0642 goc_nc_0643 goc_nc_0644 goc_nc_0645 goc_nc_0646 goc_nc_0647 goc_nc_0648 goc_nc_0649 goc_nc_0650 goc_nc_0651 goc_nc_0652 goc_nc_0653 goc_nc_0654 goc_nc_0655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
