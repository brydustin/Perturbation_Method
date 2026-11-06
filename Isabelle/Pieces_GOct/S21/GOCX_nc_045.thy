theory GOCX_nc_045
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0720: "goc_sub None 720"
  by (goc_eval goc_nc_0720)

lemma goc_nc_0721: "goc_sub None 721"
  by (goc_eval goc_nc_0721)

lemma goc_nc_0722: "goc_sub None 722"
  by (goc_eval goc_nc_0722)

lemma goc_nc_0723: "goc_sub None 723"
  by (goc_eval goc_nc_0723)

lemma goc_nc_0724: "goc_sub None 724"
  by (goc_eval goc_nc_0724)

lemma goc_nc_0725: "goc_sub None 725"
  by (goc_eval goc_nc_0725)

lemma goc_nc_0726: "goc_sub None 726"
  by (goc_eval goc_nc_0726)

lemma goc_nc_0727: "goc_sub None 727"
  by (goc_eval goc_nc_0727)

lemma goc_nc_0728: "goc_sub None 728"
  by (goc_eval goc_nc_0728)

lemma goc_nc_0729: "goc_sub None 729"
  by (goc_eval goc_nc_0729)

lemma goc_nc_0730: "goc_sub None 730"
  by (goc_eval goc_nc_0730)

lemma goc_nc_0731: "goc_sub None 731"
  by (goc_eval goc_nc_0731)

lemma goc_nc_0732: "goc_sub None 732"
  by (goc_eval goc_nc_0732)

lemma goc_nc_0733: "goc_sub None 733"
  by (goc_eval goc_nc_0733)

lemma goc_nc_0734: "goc_sub None 734"
  by (goc_eval goc_nc_0734)

lemma goc_nc_0735: "goc_sub None 735"
  by (goc_eval goc_nc_0735)

lemma gupt_nc_045: "[720..<736] = [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]"
  by (simp add: upt_rec)

lemma gsec_nc_045: "\<forall>j\<in>{16 * 45..<16 * 45 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 45..<16 * 45 + 16}"
  then have "j \<in> set [720..<736]" unfolding set_upt by simp
  then have "j \<in> set [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]" unfolding gupt_nc_045 .
  then show "goc_sub None j" using goc_nc_0720 goc_nc_0721 goc_nc_0722 goc_nc_0723 goc_nc_0724 goc_nc_0725 goc_nc_0726 goc_nc_0727 goc_nc_0728 goc_nc_0729 goc_nc_0730 goc_nc_0731 goc_nc_0732 goc_nc_0733 goc_nc_0734 goc_nc_0735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
