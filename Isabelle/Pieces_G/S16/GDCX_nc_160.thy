theory GDCX_nc_160
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2560: "gdc_sub None 2560"
  by (gdc_eval gdc_nc_2560)

lemma gdc_nc_2561: "gdc_sub None 2561"
  by (gdc_eval gdc_nc_2561)

lemma gdc_nc_2562: "gdc_sub None 2562"
  by (gdc_eval gdc_nc_2562)

lemma gdc_nc_2563: "gdc_sub None 2563"
  by (gdc_eval gdc_nc_2563)

lemma gdc_nc_2564: "gdc_sub None 2564"
  by (gdc_eval gdc_nc_2564)

lemma gdc_nc_2565: "gdc_sub None 2565"
  by (gdc_eval gdc_nc_2565)

lemma gdc_nc_2566: "gdc_sub None 2566"
  by (gdc_eval gdc_nc_2566)

lemma gdc_nc_2567: "gdc_sub None 2567"
  by (gdc_eval gdc_nc_2567)

lemma gdc_nc_2568: "gdc_sub None 2568"
  by (gdc_eval gdc_nc_2568)

lemma gdc_nc_2569: "gdc_sub None 2569"
  by (gdc_eval gdc_nc_2569)

lemma gdc_nc_2570: "gdc_sub None 2570"
  by (gdc_eval gdc_nc_2570)

lemma gdc_nc_2571: "gdc_sub None 2571"
  by (gdc_eval gdc_nc_2571)

lemma gdc_nc_2572: "gdc_sub None 2572"
  by (gdc_eval gdc_nc_2572)

lemma gdc_nc_2573: "gdc_sub None 2573"
  by (gdc_eval gdc_nc_2573)

lemma gdc_nc_2574: "gdc_sub None 2574"
  by (gdc_eval gdc_nc_2574)

lemma gdc_nc_2575: "gdc_sub None 2575"
  by (gdc_eval gdc_nc_2575)

lemma gupt_nc_160: "[2560..<2576] = [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]"
  by (simp add: upt_rec)

lemma gsec_nc_160: "\<forall>j\<in>{16 * 160..<16 * 160 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 160..<16 * 160 + 16}"
  then have "j \<in> set [2560..<2576]" unfolding set_upt by simp
  then have "j \<in> set [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]" unfolding gupt_nc_160 .
  then show "gdc_sub None j" using gdc_nc_2560 gdc_nc_2561 gdc_nc_2562 gdc_nc_2563 gdc_nc_2564 gdc_nc_2565 gdc_nc_2566 gdc_nc_2567 gdc_nc_2568 gdc_nc_2569 gdc_nc_2570 gdc_nc_2571 gdc_nc_2572 gdc_nc_2573 gdc_nc_2574 gdc_nc_2575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
