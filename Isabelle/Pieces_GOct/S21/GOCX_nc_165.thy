theory GOCX_nc_165
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2640: "goc_sub None 2640"
  by (goc_eval goc_nc_2640)

lemma goc_nc_2641: "goc_sub None 2641"
  by (goc_eval goc_nc_2641)

lemma goc_nc_2642: "goc_sub None 2642"
  by (goc_eval goc_nc_2642)

lemma goc_nc_2643: "goc_sub None 2643"
  by (goc_eval goc_nc_2643)

lemma goc_nc_2644: "goc_sub None 2644"
  by (goc_eval goc_nc_2644)

lemma goc_nc_2645: "goc_sub None 2645"
  by (goc_eval goc_nc_2645)

lemma goc_nc_2646: "goc_sub None 2646"
  by (goc_eval goc_nc_2646)

lemma goc_nc_2647: "goc_sub None 2647"
  by (goc_eval goc_nc_2647)

lemma goc_nc_2648: "goc_sub None 2648"
  by (goc_eval goc_nc_2648)

lemma goc_nc_2649: "goc_sub None 2649"
  by (goc_eval goc_nc_2649)

lemma goc_nc_2650: "goc_sub None 2650"
  by (goc_eval goc_nc_2650)

lemma goc_nc_2651: "goc_sub None 2651"
  by (goc_eval goc_nc_2651)

lemma goc_nc_2652: "goc_sub None 2652"
  by (goc_eval goc_nc_2652)

lemma goc_nc_2653: "goc_sub None 2653"
  by (goc_eval goc_nc_2653)

lemma goc_nc_2654: "goc_sub None 2654"
  by (goc_eval goc_nc_2654)

lemma goc_nc_2655: "goc_sub None 2655"
  by (goc_eval goc_nc_2655)

lemma gupt_nc_165: "[2640..<2656] = [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]"
  by (simp add: upt_rec)

lemma gsec_nc_165: "\<forall>j\<in>{16 * 165..<16 * 165 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 165..<16 * 165 + 16}"
  then have "j \<in> set [2640..<2656]" unfolding set_upt by simp
  then have "j \<in> set [2640, 2641, 2642, 2643, 2644, 2645, 2646, 2647, 2648, 2649, 2650, 2651, 2652, 2653, 2654, 2655]" unfolding gupt_nc_165 .
  then show "goc_sub None j" using goc_nc_2640 goc_nc_2641 goc_nc_2642 goc_nc_2643 goc_nc_2644 goc_nc_2645 goc_nc_2646 goc_nc_2647 goc_nc_2648 goc_nc_2649 goc_nc_2650 goc_nc_2651 goc_nc_2652 goc_nc_2653 goc_nc_2654 goc_nc_2655
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
