theory GDCX_nc_045
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0720: "gdc_sub None 720"
  by (gdc_eval gdc_nc_0720)

lemma gdc_nc_0721: "gdc_sub None 721"
  by (gdc_eval gdc_nc_0721)

lemma gdc_nc_0722: "gdc_sub None 722"
  by (gdc_eval gdc_nc_0722)

lemma gdc_nc_0723: "gdc_sub None 723"
  by (gdc_eval gdc_nc_0723)

lemma gdc_nc_0724: "gdc_sub None 724"
  by (gdc_eval gdc_nc_0724)

lemma gdc_nc_0725: "gdc_sub None 725"
  by (gdc_eval gdc_nc_0725)

lemma gdc_nc_0726: "gdc_sub None 726"
  by (gdc_eval gdc_nc_0726)

lemma gdc_nc_0727: "gdc_sub None 727"
  by (gdc_eval gdc_nc_0727)

lemma gdc_nc_0728: "gdc_sub None 728"
  by (gdc_eval gdc_nc_0728)

lemma gdc_nc_0729: "gdc_sub None 729"
  by (gdc_eval gdc_nc_0729)

lemma gdc_nc_0730: "gdc_sub None 730"
  by (gdc_eval gdc_nc_0730)

lemma gdc_nc_0731: "gdc_sub None 731"
  by (gdc_eval gdc_nc_0731)

lemma gdc_nc_0732: "gdc_sub None 732"
  by (gdc_eval gdc_nc_0732)

lemma gdc_nc_0733: "gdc_sub None 733"
  by (gdc_eval gdc_nc_0733)

lemma gdc_nc_0734: "gdc_sub None 734"
  by (gdc_eval gdc_nc_0734)

lemma gdc_nc_0735: "gdc_sub None 735"
  by (gdc_eval gdc_nc_0735)

lemma gupt_nc_045: "[720..<736] = [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]"
  by (simp add: upt_rec)

lemma gsec_nc_045: "\<forall>j\<in>{16 * 45..<16 * 45 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 45..<16 * 45 + 16}"
  then have "j \<in> set [720..<736]" unfolding set_upt by simp
  then have "j \<in> set [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]" unfolding gupt_nc_045 .
  then show "gdc_sub None j" using gdc_nc_0720 gdc_nc_0721 gdc_nc_0722 gdc_nc_0723 gdc_nc_0724 gdc_nc_0725 gdc_nc_0726 gdc_nc_0727 gdc_nc_0728 gdc_nc_0729 gdc_nc_0730 gdc_nc_0731 gdc_nc_0732 gdc_nc_0733 gdc_nc_0734 gdc_nc_0735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
