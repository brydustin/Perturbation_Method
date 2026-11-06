theory GDCX_nc_174
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2784: "gdc_sub None 2784"
  by (gdc_eval gdc_nc_2784)

lemma gdc_nc_2785: "gdc_sub None 2785"
  by (gdc_eval gdc_nc_2785)

lemma gdc_nc_2786: "gdc_sub None 2786"
  by (gdc_eval gdc_nc_2786)

lemma gdc_nc_2787: "gdc_sub None 2787"
  by (gdc_eval gdc_nc_2787)

lemma gdc_nc_2788: "gdc_sub None 2788"
  by (gdc_eval gdc_nc_2788)

lemma gdc_nc_2789: "gdc_sub None 2789"
  by (gdc_eval gdc_nc_2789)

lemma gdc_nc_2790: "gdc_sub None 2790"
  by (gdc_eval gdc_nc_2790)

lemma gdc_nc_2791: "gdc_sub None 2791"
  by (gdc_eval gdc_nc_2791)

lemma gdc_nc_2792: "gdc_sub None 2792"
  by (gdc_eval gdc_nc_2792)

lemma gdc_nc_2793: "gdc_sub None 2793"
  by (gdc_eval gdc_nc_2793)

lemma gdc_nc_2794: "gdc_sub None 2794"
  by (gdc_eval gdc_nc_2794)

lemma gdc_nc_2795: "gdc_sub None 2795"
  by (gdc_eval gdc_nc_2795)

lemma gdc_nc_2796: "gdc_sub None 2796"
  by (gdc_eval gdc_nc_2796)

lemma gdc_nc_2797: "gdc_sub None 2797"
  by (gdc_eval gdc_nc_2797)

lemma gdc_nc_2798: "gdc_sub None 2798"
  by (gdc_eval gdc_nc_2798)

lemma gdc_nc_2799: "gdc_sub None 2799"
  by (gdc_eval gdc_nc_2799)

lemma gupt_nc_174: "[2784..<2800] = [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]"
  by (simp add: upt_rec)

lemma gsec_nc_174: "\<forall>j\<in>{16 * 174..<16 * 174 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 174..<16 * 174 + 16}"
  then have "j \<in> set [2784..<2800]" unfolding set_upt by simp
  then have "j \<in> set [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]" unfolding gupt_nc_174 .
  then show "gdc_sub None j" using gdc_nc_2784 gdc_nc_2785 gdc_nc_2786 gdc_nc_2787 gdc_nc_2788 gdc_nc_2789 gdc_nc_2790 gdc_nc_2791 gdc_nc_2792 gdc_nc_2793 gdc_nc_2794 gdc_nc_2795 gdc_nc_2796 gdc_nc_2797 gdc_nc_2798 gdc_nc_2799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
