theory GOCX_nc_160
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2560: "goc_sub None 2560"
  by (goc_eval goc_nc_2560)

lemma goc_nc_2561: "goc_sub None 2561"
  by (goc_eval goc_nc_2561)

lemma goc_nc_2562: "goc_sub None 2562"
  by (goc_eval goc_nc_2562)

lemma goc_nc_2563: "goc_sub None 2563"
  by (goc_eval goc_nc_2563)

lemma goc_nc_2564: "goc_sub None 2564"
  by (goc_eval goc_nc_2564)

lemma goc_nc_2565: "goc_sub None 2565"
  by (goc_eval goc_nc_2565)

lemma goc_nc_2566: "goc_sub None 2566"
  by (goc_eval goc_nc_2566)

lemma goc_nc_2567: "goc_sub None 2567"
  by (goc_eval goc_nc_2567)

lemma goc_nc_2568: "goc_sub None 2568"
  by (goc_eval goc_nc_2568)

lemma goc_nc_2569: "goc_sub None 2569"
  by (goc_eval goc_nc_2569)

lemma goc_nc_2570: "goc_sub None 2570"
  by (goc_eval goc_nc_2570)

lemma goc_nc_2571: "goc_sub None 2571"
  by (goc_eval goc_nc_2571)

lemma goc_nc_2572: "goc_sub None 2572"
  by (goc_eval goc_nc_2572)

lemma goc_nc_2573: "goc_sub None 2573"
  by (goc_eval goc_nc_2573)

lemma goc_nc_2574: "goc_sub None 2574"
  by (goc_eval goc_nc_2574)

lemma goc_nc_2575: "goc_sub None 2575"
  by (goc_eval goc_nc_2575)

lemma gupt_nc_160: "[2560..<2576] = [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]"
  by (simp add: upt_rec)

lemma gsec_nc_160: "\<forall>j\<in>{16 * 160..<16 * 160 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 160..<16 * 160 + 16}"
  then have "j \<in> set [2560..<2576]" unfolding set_upt by simp
  then have "j \<in> set [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]" unfolding gupt_nc_160 .
  then show "goc_sub None j" using goc_nc_2560 goc_nc_2561 goc_nc_2562 goc_nc_2563 goc_nc_2564 goc_nc_2565 goc_nc_2566 goc_nc_2567 goc_nc_2568 goc_nc_2569 goc_nc_2570 goc_nc_2571 goc_nc_2572 goc_nc_2573 goc_nc_2574 goc_nc_2575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
