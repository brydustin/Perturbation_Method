theory GDCX_nc_167
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2672: "gdc_sub None 2672"
  by (gdc_eval gdc_nc_2672)

lemma gdc_nc_2673: "gdc_sub None 2673"
  by (gdc_eval gdc_nc_2673)

lemma gdc_nc_2674: "gdc_sub None 2674"
  by (gdc_eval gdc_nc_2674)

lemma gdc_nc_2675: "gdc_sub None 2675"
  by (gdc_eval gdc_nc_2675)

lemma gdc_nc_2676: "gdc_sub None 2676"
  by (gdc_eval gdc_nc_2676)

lemma gdc_nc_2677: "gdc_sub None 2677"
  by (gdc_eval gdc_nc_2677)

lemma gdc_nc_2678: "gdc_sub None 2678"
  by (gdc_eval gdc_nc_2678)

lemma gdc_nc_2679: "gdc_sub None 2679"
  by (gdc_eval gdc_nc_2679)

lemma gdc_nc_2680: "gdc_sub None 2680"
  by (gdc_eval gdc_nc_2680)

lemma gdc_nc_2681: "gdc_sub None 2681"
  by (gdc_eval gdc_nc_2681)

lemma gdc_nc_2682: "gdc_sub None 2682"
  by (gdc_eval gdc_nc_2682)

lemma gdc_nc_2683: "gdc_sub None 2683"
  by (gdc_eval gdc_nc_2683)

lemma gdc_nc_2684: "gdc_sub None 2684"
  by (gdc_eval gdc_nc_2684)

lemma gdc_nc_2685: "gdc_sub None 2685"
  by (gdc_eval gdc_nc_2685)

lemma gdc_nc_2686: "gdc_sub None 2686"
  by (gdc_eval gdc_nc_2686)

lemma gdc_nc_2687: "gdc_sub None 2687"
  by (gdc_eval gdc_nc_2687)

lemma gupt_nc_167: "[2672..<2688] = [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]"
  by (simp add: upt_rec)

lemma gsec_nc_167: "\<forall>j\<in>{16 * 167..<16 * 167 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 167..<16 * 167 + 16}"
  then have "j \<in> set [2672..<2688]" unfolding set_upt by simp
  then have "j \<in> set [2672, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2683, 2684, 2685, 2686, 2687]" unfolding gupt_nc_167 .
  then show "gdc_sub None j" using gdc_nc_2672 gdc_nc_2673 gdc_nc_2674 gdc_nc_2675 gdc_nc_2676 gdc_nc_2677 gdc_nc_2678 gdc_nc_2679 gdc_nc_2680 gdc_nc_2681 gdc_nc_2682 gdc_nc_2683 gdc_nc_2684 gdc_nc_2685 gdc_nc_2686 gdc_nc_2687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
