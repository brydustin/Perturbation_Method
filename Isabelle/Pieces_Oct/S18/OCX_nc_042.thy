theory OCX_nc_042
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0672: "oc_sub None 672"
  by (oc_eval oc_nc_0672)

lemma oc_nc_0673: "oc_sub None 673"
  by (oc_eval oc_nc_0673)

lemma oc_nc_0674: "oc_sub None 674"
  by (oc_eval oc_nc_0674)

lemma oc_nc_0675: "oc_sub None 675"
  by (oc_eval oc_nc_0675)

lemma oc_nc_0676: "oc_sub None 676"
  by (oc_eval oc_nc_0676)

lemma oc_nc_0677: "oc_sub None 677"
  by (oc_eval oc_nc_0677)

lemma oc_nc_0678: "oc_sub None 678"
  by (oc_eval oc_nc_0678)

lemma oc_nc_0679: "oc_sub None 679"
  by (oc_eval oc_nc_0679)

lemma oc_nc_0680: "oc_sub None 680"
  by (oc_eval oc_nc_0680)

lemma oc_nc_0681: "oc_sub None 681"
  by (oc_eval oc_nc_0681)

lemma oc_nc_0682: "oc_sub None 682"
  by (oc_eval oc_nc_0682)

lemma oc_nc_0683: "oc_sub None 683"
  by (oc_eval oc_nc_0683)

lemma oc_nc_0684: "oc_sub None 684"
  by (oc_eval oc_nc_0684)

lemma oc_nc_0685: "oc_sub None 685"
  by (oc_eval oc_nc_0685)

lemma oc_nc_0686: "oc_sub None 686"
  by (oc_eval oc_nc_0686)

lemma oc_nc_0687: "oc_sub None 687"
  by (oc_eval oc_nc_0687)

lemma upt_nc_042: "[672..<688] = [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]"
  by (simp add: upt_rec)

lemma sec_nc_042: "\<forall>j\<in>{16 * 42..<16 * 42 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 42..<16 * 42 + 16}"
  then have "j \<in> set [672..<688]" unfolding set_upt by simp
  then have "j \<in> set [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]" unfolding upt_nc_042 .
  then show "oc_sub None j" using oc_nc_0672 oc_nc_0673 oc_nc_0674 oc_nc_0675 oc_nc_0676 oc_nc_0677 oc_nc_0678 oc_nc_0679 oc_nc_0680 oc_nc_0681 oc_nc_0682 oc_nc_0683 oc_nc_0684 oc_nc_0685 oc_nc_0686 oc_nc_0687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
