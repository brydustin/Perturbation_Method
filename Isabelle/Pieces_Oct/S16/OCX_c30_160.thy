theory OCX_c30_160
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2560: "oc_sub oc_b30 2560"
  by (oc_eval oc_c30_2560)

lemma oc_c30_2561: "oc_sub oc_b30 2561"
  by (oc_eval oc_c30_2561)

lemma oc_c30_2562: "oc_sub oc_b30 2562"
  by (oc_eval oc_c30_2562)

lemma oc_c30_2563: "oc_sub oc_b30 2563"
  by (oc_eval oc_c30_2563)

lemma oc_c30_2564: "oc_sub oc_b30 2564"
  by (oc_eval oc_c30_2564)

lemma oc_c30_2565: "oc_sub oc_b30 2565"
  by (oc_eval oc_c30_2565)

lemma oc_c30_2566: "oc_sub oc_b30 2566"
  by (oc_eval oc_c30_2566)

lemma oc_c30_2567: "oc_sub oc_b30 2567"
  by (oc_eval oc_c30_2567)

lemma oc_c30_2568: "oc_sub oc_b30 2568"
  by (oc_eval oc_c30_2568)

lemma oc_c30_2569: "oc_sub oc_b30 2569"
  by (oc_eval oc_c30_2569)

lemma oc_c30_2570: "oc_sub oc_b30 2570"
  by (oc_eval oc_c30_2570)

lemma oc_c30_2571: "oc_sub oc_b30 2571"
  by (oc_eval oc_c30_2571)

lemma oc_c30_2572: "oc_sub oc_b30 2572"
  by (oc_eval oc_c30_2572)

lemma oc_c30_2573: "oc_sub oc_b30 2573"
  by (oc_eval oc_c30_2573)

lemma oc_c30_2574: "oc_sub oc_b30 2574"
  by (oc_eval oc_c30_2574)

lemma oc_c30_2575: "oc_sub oc_b30 2575"
  by (oc_eval oc_c30_2575)

lemma upt_c30_160: "[2560..<2576] = [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]"
  by (simp add: upt_rec)

lemma sec_c30_160: "\<forall>j\<in>{16 * 160..<16 * 160 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 160..<16 * 160 + 16}"
  then have "j \<in> set [2560..<2576]" unfolding set_upt by simp
  then have "j \<in> set [2560, 2561, 2562, 2563, 2564, 2565, 2566, 2567, 2568, 2569, 2570, 2571, 2572, 2573, 2574, 2575]" unfolding upt_c30_160 .
  then show "oc_sub oc_b30 j" using oc_c30_2560 oc_c30_2561 oc_c30_2562 oc_c30_2563 oc_c30_2564 oc_c30_2565 oc_c30_2566 oc_c30_2567 oc_c30_2568 oc_c30_2569 oc_c30_2570 oc_c30_2571 oc_c30_2572 oc_c30_2573 oc_c30_2574 oc_c30_2575
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
