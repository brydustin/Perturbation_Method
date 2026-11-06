theory GDCX_nc_040
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0640: "gdc_sub None 640"
  by (gdc_eval gdc_nc_0640)

lemma gdc_nc_0641: "gdc_sub None 641"
  by (gdc_eval gdc_nc_0641)

lemma gdc_nc_0642: "gdc_sub None 642"
  by (gdc_eval gdc_nc_0642)

lemma gdc_nc_0643: "gdc_sub None 643"
  by (gdc_eval gdc_nc_0643)

lemma gdc_nc_0644: "gdc_sub None 644"
  by (gdc_eval gdc_nc_0644)

lemma gdc_nc_0645: "gdc_sub None 645"
  by (gdc_eval gdc_nc_0645)

lemma gdc_nc_0646: "gdc_sub None 646"
  by (gdc_eval gdc_nc_0646)

lemma gdc_nc_0647: "gdc_sub None 647"
  by (gdc_eval gdc_nc_0647)

lemma gdc_nc_0648: "gdc_sub None 648"
  by (gdc_eval gdc_nc_0648)

lemma gdc_nc_0649: "gdc_sub None 649"
  by (gdc_eval gdc_nc_0649)

lemma gdc_nc_0650: "gdc_sub None 650"
  by (gdc_eval gdc_nc_0650)

lemma gdc_nc_0651: "gdc_sub None 651"
  by (gdc_eval gdc_nc_0651)

lemma gdc_nc_0652: "gdc_sub None 652"
  by (gdc_eval gdc_nc_0652)

lemma gdc_nc_0653: "gdc_sub None 653"
  by (gdc_eval gdc_nc_0653)

lemma gdc_nc_0654: "gdc_sub None 654"
  by (gdc_eval gdc_nc_0654)

lemma gdc_nc_0655: "gdc_sub None 655"
  by (gdc_eval gdc_nc_0655)

lemma gupt_nc_040: "[640..<656] = [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]"
  by (simp add: upt_rec)

lemma gsec_nc_040: "\<forall>j\<in>{16 * 40..<16 * 40 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 40..<16 * 40 + 16}"
  then have "j \<in> set [640..<656]" unfolding set_upt by simp
  then have "j \<in> set [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655]" unfolding gupt_nc_040 .
  then show "gdc_sub None j" using gdc_nc_0640 gdc_nc_0641 gdc_nc_0642 gdc_nc_0643 gdc_nc_0644 gdc_nc_0645 gdc_nc_0646 gdc_nc_0647 gdc_nc_0648 gdc_nc_0649 gdc_nc_0650 gdc_nc_0651 gdc_nc_0652 gdc_nc_0653 gdc_nc_0654 gdc_nc_0655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
