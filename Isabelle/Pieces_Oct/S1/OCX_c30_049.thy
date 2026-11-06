theory OCX_c30_049
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0784: "oc_sub oc_b30 784"
  by (oc_eval oc_c30_0784)

lemma oc_c30_0785: "oc_sub oc_b30 785"
  by (oc_eval oc_c30_0785)

lemma oc_c30_0786: "oc_sub oc_b30 786"
  by (oc_eval oc_c30_0786)

lemma oc_c30_0787: "oc_sub oc_b30 787"
  by (oc_eval oc_c30_0787)

lemma oc_c30_0788: "oc_sub oc_b30 788"
  by (oc_eval oc_c30_0788)

lemma oc_c30_0789: "oc_sub oc_b30 789"
  by (oc_eval oc_c30_0789)

lemma oc_c30_0790: "oc_sub oc_b30 790"
  by (oc_eval oc_c30_0790)

lemma oc_c30_0791: "oc_sub oc_b30 791"
  by (oc_eval oc_c30_0791)

lemma oc_c30_0792: "oc_sub oc_b30 792"
  by (oc_eval oc_c30_0792)

lemma oc_c30_0793: "oc_sub oc_b30 793"
  by (oc_eval oc_c30_0793)

lemma oc_c30_0794: "oc_sub oc_b30 794"
  by (oc_eval oc_c30_0794)

lemma oc_c30_0795: "oc_sub oc_b30 795"
  by (oc_eval oc_c30_0795)

lemma oc_c30_0796: "oc_sub oc_b30 796"
  by (oc_eval oc_c30_0796)

lemma oc_c30_0797: "oc_sub oc_b30 797"
  by (oc_eval oc_c30_0797)

lemma oc_c30_0798: "oc_sub oc_b30 798"
  by (oc_eval oc_c30_0798)

lemma oc_c30_0799: "oc_sub oc_b30 799"
  by (oc_eval oc_c30_0799)

lemma upt_c30_049: "[784..<800] = [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]"
  by (simp add: upt_rec)

lemma sec_c30_049: "\<forall>j\<in>{16 * 49..<16 * 49 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 49..<16 * 49 + 16}"
  then have "j \<in> set [784..<800]" unfolding set_upt by simp
  then have "j \<in> set [784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799]" unfolding upt_c30_049 .
  then show "oc_sub oc_b30 j" using oc_c30_0784 oc_c30_0785 oc_c30_0786 oc_c30_0787 oc_c30_0788 oc_c30_0789 oc_c30_0790 oc_c30_0791 oc_c30_0792 oc_c30_0793 oc_c30_0794 oc_c30_0795 oc_c30_0796 oc_c30_0797 oc_c30_0798 oc_c30_0799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
