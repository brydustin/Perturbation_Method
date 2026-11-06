theory DCX_nc_045
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0720: "dc_sub None 720"
  by (dc_eval dc_nc_0720)

lemma dc_nc_0721: "dc_sub None 721"
  by (dc_eval dc_nc_0721)

lemma dc_nc_0722: "dc_sub None 722"
  by (dc_eval dc_nc_0722)

lemma dc_nc_0723: "dc_sub None 723"
  by (dc_eval dc_nc_0723)

lemma dc_nc_0724: "dc_sub None 724"
  by (dc_eval dc_nc_0724)

lemma dc_nc_0725: "dc_sub None 725"
  by (dc_eval dc_nc_0725)

lemma dc_nc_0726: "dc_sub None 726"
  by (dc_eval dc_nc_0726)

lemma dc_nc_0727: "dc_sub None 727"
  by (dc_eval dc_nc_0727)

lemma dc_nc_0728: "dc_sub None 728"
  by (dc_eval dc_nc_0728)

lemma dc_nc_0729: "dc_sub None 729"
  by (dc_eval dc_nc_0729)

lemma dc_nc_0730: "dc_sub None 730"
  by (dc_eval dc_nc_0730)

lemma dc_nc_0731: "dc_sub None 731"
  by (dc_eval dc_nc_0731)

lemma dc_nc_0732: "dc_sub None 732"
  by (dc_eval dc_nc_0732)

lemma dc_nc_0733: "dc_sub None 733"
  by (dc_eval dc_nc_0733)

lemma dc_nc_0734: "dc_sub None 734"
  by (dc_eval dc_nc_0734)

lemma dc_nc_0735: "dc_sub None 735"
  by (dc_eval dc_nc_0735)

lemma upt_nc_045: "[720..<736] = [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]"
  by (simp add: upt_rec)

lemma sec_nc_045: "\<forall>j\<in>{16 * 45..<16 * 45 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 45..<16 * 45 + 16}"
  then have "j \<in> set [720..<736]" unfolding set_upt by simp
  then have "j \<in> set [720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]" unfolding upt_nc_045 .
  then show "dc_sub None j" using dc_nc_0720 dc_nc_0721 dc_nc_0722 dc_nc_0723 dc_nc_0724 dc_nc_0725 dc_nc_0726 dc_nc_0727 dc_nc_0728 dc_nc_0729 dc_nc_0730 dc_nc_0731 dc_nc_0732 dc_nc_0733 dc_nc_0734 dc_nc_0735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
