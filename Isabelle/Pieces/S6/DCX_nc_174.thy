theory DCX_nc_174
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2784: "dc_sub None 2784"
  by (dc_eval dc_nc_2784)

lemma dc_nc_2785: "dc_sub None 2785"
  by (dc_eval dc_nc_2785)

lemma dc_nc_2786: "dc_sub None 2786"
  by (dc_eval dc_nc_2786)

lemma dc_nc_2787: "dc_sub None 2787"
  by (dc_eval dc_nc_2787)

lemma dc_nc_2788: "dc_sub None 2788"
  by (dc_eval dc_nc_2788)

lemma dc_nc_2789: "dc_sub None 2789"
  by (dc_eval dc_nc_2789)

lemma dc_nc_2790: "dc_sub None 2790"
  by (dc_eval dc_nc_2790)

lemma dc_nc_2791: "dc_sub None 2791"
  by (dc_eval dc_nc_2791)

lemma dc_nc_2792: "dc_sub None 2792"
  by (dc_eval dc_nc_2792)

lemma dc_nc_2793: "dc_sub None 2793"
  by (dc_eval dc_nc_2793)

lemma dc_nc_2794: "dc_sub None 2794"
  by (dc_eval dc_nc_2794)

lemma dc_nc_2795: "dc_sub None 2795"
  by (dc_eval dc_nc_2795)

lemma dc_nc_2796: "dc_sub None 2796"
  by (dc_eval dc_nc_2796)

lemma dc_nc_2797: "dc_sub None 2797"
  by (dc_eval dc_nc_2797)

lemma dc_nc_2798: "dc_sub None 2798"
  by (dc_eval dc_nc_2798)

lemma dc_nc_2799: "dc_sub None 2799"
  by (dc_eval dc_nc_2799)

lemma upt_nc_174: "[2784..<2800] = [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]"
  by (simp add: upt_rec)

lemma sec_nc_174: "\<forall>j\<in>{16 * 174..<16 * 174 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 174..<16 * 174 + 16}"
  then have "j \<in> set [2784..<2800]" unfolding set_upt by simp
  then have "j \<in> set [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]" unfolding upt_nc_174 .
  then show "dc_sub None j" using dc_nc_2784 dc_nc_2785 dc_nc_2786 dc_nc_2787 dc_nc_2788 dc_nc_2789 dc_nc_2790 dc_nc_2791 dc_nc_2792 dc_nc_2793 dc_nc_2794 dc_nc_2795 dc_nc_2796 dc_nc_2797 dc_nc_2798 dc_nc_2799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
