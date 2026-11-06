theory DCX_nc_042
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0672: "dc_sub None 672"
  by (dc_eval dc_nc_0672)

lemma dc_nc_0673: "dc_sub None 673"
  by (dc_eval dc_nc_0673)

lemma dc_nc_0674: "dc_sub None 674"
  by (dc_eval dc_nc_0674)

lemma dc_nc_0675: "dc_sub None 675"
  by (dc_eval dc_nc_0675)

lemma dc_nc_0676: "dc_sub None 676"
  by (dc_eval dc_nc_0676)

lemma dc_nc_0677: "dc_sub None 677"
  by (dc_eval dc_nc_0677)

lemma dc_nc_0678: "dc_sub None 678"
  by (dc_eval dc_nc_0678)

lemma dc_nc_0679: "dc_sub None 679"
  by (dc_eval dc_nc_0679)

lemma dc_nc_0680: "dc_sub None 680"
  by (dc_eval dc_nc_0680)

lemma dc_nc_0681: "dc_sub None 681"
  by (dc_eval dc_nc_0681)

lemma dc_nc_0682: "dc_sub None 682"
  by (dc_eval dc_nc_0682)

lemma dc_nc_0683: "dc_sub None 683"
  by (dc_eval dc_nc_0683)

lemma dc_nc_0684: "dc_sub None 684"
  by (dc_eval dc_nc_0684)

lemma dc_nc_0685: "dc_sub None 685"
  by (dc_eval dc_nc_0685)

lemma dc_nc_0686: "dc_sub None 686"
  by (dc_eval dc_nc_0686)

lemma dc_nc_0687: "dc_sub None 687"
  by (dc_eval dc_nc_0687)

lemma upt_nc_042: "[672..<688] = [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]"
  by (simp add: upt_rec)

lemma sec_nc_042: "\<forall>j\<in>{16 * 42..<16 * 42 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 42..<16 * 42 + 16}"
  then have "j \<in> set [672..<688]" unfolding set_upt by simp
  then have "j \<in> set [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]" unfolding upt_nc_042 .
  then show "dc_sub None j" using dc_nc_0672 dc_nc_0673 dc_nc_0674 dc_nc_0675 dc_nc_0676 dc_nc_0677 dc_nc_0678 dc_nc_0679 dc_nc_0680 dc_nc_0681 dc_nc_0682 dc_nc_0683 dc_nc_0684 dc_nc_0685 dc_nc_0686 dc_nc_0687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
