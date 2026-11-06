theory OCX_nc_160
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2560: "oc_sub None 2560"
  by (oc_eval oc_nc_2560)

lemma oc_nc_2561: "oc_sub None 2561"
  by (oc_eval oc_nc_2561)

lemma oc_nc_2562: "oc_sub None 2562"
  by (oc_eval oc_nc_2562)

lemma oc_nc_2563: "oc_sub None 2563"
  by (oc_eval oc_nc_2563)

lemma oc_nc_2564: "oc_sub None 2564"
  by (oc_eval oc_nc_2564)

lemma oc_nc_2565: "oc_sub None 2565"
  by (oc_eval oc_nc_2565)

lemma oc_nc_2566: "oc_sub None 2566"
  by (oc_eval oc_nc_2566)

lemma oc_nc_2567: "oc_sub None 2567"
  by (oc_eval oc_nc_2567)

lemma oc_nc_2568: "oc_sub None 2568"
  by (oc_eval oc_nc_2568)

lemma oc_nc_2569: "oc_sub None 2569"
  by (oc_eval oc_nc_2569)

lemma oc_nc_2570: "oc_sub None 2570"
  by (oc_eval oc_nc_2570)

lemma oc_nc_2571: "oc_sub None 2571"
  by (oc_eval oc_nc_2571)

lemma oc_nc_2572: "oc_sub None 2572"
  by (oc_eval oc_nc_2572)

lemma oc_nc_2573: "oc_sub None 2573"
  by (oc_eval oc_nc_2573)

lemma oc_nc_2574: "oc_sub None 2574"
  by (oc_eval oc_nc_2574)

lemma oc_nc_2575: "oc_sub None 2575"
  by (oc_eval oc_nc_2575)

lemma upt_nc_160: "[2560..<2576] = [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]"
  by (simp add: upt_rec)

lemma sec_nc_160: "\<forall>j\<in>{16 * 160..<16 * 160 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 160..<16 * 160 + 16}"
  then have "j \<in> set [2560..<2576]" unfolding set_upt by simp
  then have "j \<in> set [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]" unfolding upt_nc_160 .
  then show "oc_sub None j" using oc_nc_2560 oc_nc_2561 oc_nc_2562 oc_nc_2563 oc_nc_2564 oc_nc_2565 oc_nc_2566 oc_nc_2567 oc_nc_2568 oc_nc_2569 oc_nc_2570 oc_nc_2571 oc_nc_2572 oc_nc_2573 oc_nc_2574 oc_nc_2575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
