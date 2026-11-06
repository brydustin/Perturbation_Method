theory GDCX_nc_165
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2640: "gdc_sub None 2640"
  by (gdc_eval gdc_nc_2640)

lemma gdc_nc_2641: "gdc_sub None 2641"
  by (gdc_eval gdc_nc_2641)

lemma gdc_nc_2642: "gdc_sub None 2642"
  by (gdc_eval gdc_nc_2642)

lemma gdc_nc_2643: "gdc_sub None 2643"
  by (gdc_eval gdc_nc_2643)

lemma gdc_nc_2644: "gdc_sub None 2644"
  by (gdc_eval gdc_nc_2644)

lemma gdc_nc_2645: "gdc_sub None 2645"
  by (gdc_eval gdc_nc_2645)

lemma gdc_nc_2646: "gdc_sub None 2646"
  by (gdc_eval gdc_nc_2646)

lemma gdc_nc_2647: "gdc_sub None 2647"
  by (gdc_eval gdc_nc_2647)

lemma gdc_nc_2648: "gdc_sub None 2648"
  by (gdc_eval gdc_nc_2648)

lemma gdc_nc_2649: "gdc_sub None 2649"
  by (gdc_eval gdc_nc_2649)

lemma gdc_nc_2650: "gdc_sub None 2650"
  by (gdc_eval gdc_nc_2650)

lemma gdc_nc_2651: "gdc_sub None 2651"
  by (gdc_eval gdc_nc_2651)

lemma gdc_nc_2652: "gdc_sub None 2652"
  by (gdc_eval gdc_nc_2652)

lemma gdc_nc_2653: "gdc_sub None 2653"
  by (gdc_eval gdc_nc_2653)

lemma gdc_nc_2654: "gdc_sub None 2654"
  by (gdc_eval gdc_nc_2654)

lemma gdc_nc_2655: "gdc_sub None 2655"
  by (gdc_eval gdc_nc_2655)

lemma gupt_nc_165: "[2640..<2656] = [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]"
  by (simp add: upt_rec)

lemma gsec_nc_165: "\<forall>j\<in>{16 * 165..<16 * 165 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 165..<16 * 165 + 16}"
  then have "j \<in> set [2640..<2656]" unfolding set_upt by simp
  then have "j \<in> set [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]" unfolding gupt_nc_165 .
  then show "gdc_sub None j" using gdc_nc_2640 gdc_nc_2641 gdc_nc_2642 gdc_nc_2643 gdc_nc_2644 gdc_nc_2645 gdc_nc_2646 gdc_nc_2647 gdc_nc_2648 gdc_nc_2649 gdc_nc_2650 gdc_nc_2651 gdc_nc_2652 gdc_nc_2653 gdc_nc_2654 gdc_nc_2655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
