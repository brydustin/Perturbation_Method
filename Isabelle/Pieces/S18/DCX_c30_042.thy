theory DCX_c30_042
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0672: "dc_sub dc_b30 672"
  by (dc_eval dc_c30_0672)

lemma dc_c30_0673: "dc_sub dc_b30 673"
  by (dc_eval dc_c30_0673)

lemma dc_c30_0674: "dc_sub dc_b30 674"
  by (dc_eval dc_c30_0674)

lemma dc_c30_0675: "dc_sub dc_b30 675"
  by (dc_eval dc_c30_0675)

lemma dc_c30_0676: "dc_sub dc_b30 676"
  by (dc_eval dc_c30_0676)

lemma dc_c30_0677: "dc_sub dc_b30 677"
  by (dc_eval dc_c30_0677)

lemma dc_c30_0678: "dc_sub dc_b30 678"
  by (dc_eval dc_c30_0678)

lemma dc_c30_0679: "dc_sub dc_b30 679"
  by (dc_eval dc_c30_0679)

lemma dc_c30_0680: "dc_sub dc_b30 680"
  by (dc_eval dc_c30_0680)

lemma dc_c30_0681: "dc_sub dc_b30 681"
  by (dc_eval dc_c30_0681)

lemma dc_c30_0682: "dc_sub dc_b30 682"
  by (dc_eval dc_c30_0682)

lemma dc_c30_0683: "dc_sub dc_b30 683"
  by (dc_eval dc_c30_0683)

lemma dc_c30_0684: "dc_sub dc_b30 684"
  by (dc_eval dc_c30_0684)

lemma dc_c30_0685: "dc_sub dc_b30 685"
  by (dc_eval dc_c30_0685)

lemma dc_c30_0686: "dc_sub dc_b30 686"
  by (dc_eval dc_c30_0686)

lemma dc_c30_0687: "dc_sub dc_b30 687"
  by (dc_eval dc_c30_0687)

lemma upt_c30_042: "[672..<688] = [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]"
  by (simp add: upt_rec)

lemma sec_c30_042: "\<forall>j\<in>{16 * 42..<16 * 42 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 42..<16 * 42 + 16}"
  then have "j \<in> set [672..<688]" unfolding set_upt by simp
  then have "j \<in> set [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]" unfolding upt_c30_042 .
  then show "dc_sub dc_b30 j" using dc_c30_0672 dc_c30_0673 dc_c30_0674 dc_c30_0675 dc_c30_0676 dc_c30_0677 dc_c30_0678 dc_c30_0679 dc_c30_0680 dc_c30_0681 dc_c30_0682 dc_c30_0683 dc_c30_0684 dc_c30_0685 dc_c30_0686 dc_c30_0687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
