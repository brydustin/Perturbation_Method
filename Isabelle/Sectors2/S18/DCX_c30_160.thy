theory DCX_c30_160
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2560: "dc_sub dc_b30 2560"
  by (dc_eval dc_c30_2560)

lemma dc_c30_2561: "dc_sub dc_b30 2561"
  by (dc_eval dc_c30_2561)

lemma dc_c30_2562: "dc_sub dc_b30 2562"
  by (dc_eval dc_c30_2562)

lemma dc_c30_2563: "dc_sub dc_b30 2563"
  by (dc_eval dc_c30_2563)

lemma dc_c30_2564: "dc_sub dc_b30 2564"
  by (dc_eval dc_c30_2564)

lemma dc_c30_2565: "dc_sub dc_b30 2565"
  by (dc_eval dc_c30_2565)

lemma dc_c30_2566: "dc_sub dc_b30 2566"
  by (dc_eval dc_c30_2566)

lemma dc_c30_2567: "dc_sub dc_b30 2567"
  by (dc_eval dc_c30_2567)

lemma dc_c30_2568: "dc_sub dc_b30 2568"
  by (dc_eval dc_c30_2568)

lemma dc_c30_2569: "dc_sub dc_b30 2569"
  by (dc_eval dc_c30_2569)

lemma dc_c30_2570: "dc_sub dc_b30 2570"
  by (dc_eval dc_c30_2570)

lemma dc_c30_2571: "dc_sub dc_b30 2571"
  by (dc_eval dc_c30_2571)

lemma dc_c30_2572: "dc_sub dc_b30 2572"
  by (dc_eval dc_c30_2572)

lemma dc_c30_2573: "dc_sub dc_b30 2573"
  by (dc_eval dc_c30_2573)

lemma dc_c30_2574: "dc_sub dc_b30 2574"
  by (dc_eval dc_c30_2574)

lemma dc_c30_2575: "dc_sub dc_b30 2575"
  by (dc_eval dc_c30_2575)

lemma upt_c30_160: "[2560..<2576] = [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]"
  by (simp add: upt_rec)

lemma sec_c30_160: "\<forall>j\<in>{16 * 160..<16 * 160 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 160..<16 * 160 + 16}"
  then have "j \<in> set [2560..<2576]" unfolding set_upt by simp
  then have "j \<in> set [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]" unfolding upt_c30_160 .
  then show "dc_sub dc_b30 j" using dc_c30_2560 dc_c30_2561 dc_c30_2562 dc_c30_2563 dc_c30_2564 dc_c30_2565 dc_c30_2566 dc_c30_2567 dc_c30_2568 dc_c30_2569 dc_c30_2570 dc_c30_2571 dc_c30_2572 dc_c30_2573 dc_c30_2574 dc_c30_2575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
