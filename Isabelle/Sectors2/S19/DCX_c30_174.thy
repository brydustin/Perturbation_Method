theory DCX_c30_174
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2784: "dc_sub dc_b30 2784"
  by (dc_eval dc_c30_2784)

lemma dc_c30_2785: "dc_sub dc_b30 2785"
  by (dc_eval dc_c30_2785)

lemma dc_c30_2786: "dc_sub dc_b30 2786"
  by (dc_eval dc_c30_2786)

lemma dc_c30_2787: "dc_sub dc_b30 2787"
  by (dc_eval dc_c30_2787)

lemma dc_c30_2788: "dc_sub dc_b30 2788"
  by (dc_eval dc_c30_2788)

lemma dc_c30_2789: "dc_sub dc_b30 2789"
  by (dc_eval dc_c30_2789)

lemma dc_c30_2790: "dc_sub dc_b30 2790"
  by (dc_eval dc_c30_2790)

lemma dc_c30_2791: "dc_sub dc_b30 2791"
  by (dc_eval dc_c30_2791)

lemma dc_c30_2792: "dc_sub dc_b30 2792"
  by (dc_eval dc_c30_2792)

lemma dc_c30_2793: "dc_sub dc_b30 2793"
  by (dc_eval dc_c30_2793)

lemma dc_c30_2794: "dc_sub dc_b30 2794"
  by (dc_eval dc_c30_2794)

lemma dc_c30_2795: "dc_sub dc_b30 2795"
  by (dc_eval dc_c30_2795)

lemma dc_c30_2796: "dc_sub dc_b30 2796"
  by (dc_eval dc_c30_2796)

lemma dc_c30_2797: "dc_sub dc_b30 2797"
  by (dc_eval dc_c30_2797)

lemma dc_c30_2798: "dc_sub dc_b30 2798"
  by (dc_eval dc_c30_2798)

lemma dc_c30_2799: "dc_sub dc_b30 2799"
  by (dc_eval dc_c30_2799)

lemma upt_c30_174: "[2784..<2800] = [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]"
  by (simp add: upt_rec)

lemma sec_c30_174: "\<forall>j\<in>{16 * 174..<16 * 174 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 174..<16 * 174 + 16}"
  then have "j \<in> set [2784..<2800]" unfolding set_upt by simp
  then have "j \<in> set [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]" unfolding upt_c30_174 .
  then show "dc_sub dc_b30 j" using dc_c30_2784 dc_c30_2785 dc_c30_2786 dc_c30_2787 dc_c30_2788 dc_c30_2789 dc_c30_2790 dc_c30_2791 dc_c30_2792 dc_c30_2793 dc_c30_2794 dc_c30_2795 dc_c30_2796 dc_c30_2797 dc_c30_2798 dc_c30_2799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
