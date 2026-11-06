theory OCX_c30_175
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2800: "oc_sub oc_b30 2800"
  by (oc_eval oc_c30_2800)

lemma oc_c30_2801: "oc_sub oc_b30 2801"
  by (oc_eval oc_c30_2801)

lemma oc_c30_2802: "oc_sub oc_b30 2802"
  by (oc_eval oc_c30_2802)

lemma oc_c30_2803: "oc_sub oc_b30 2803"
  by (oc_eval oc_c30_2803)

lemma oc_c30_2804: "oc_sub oc_b30 2804"
  by (oc_eval oc_c30_2804)

lemma oc_c30_2805: "oc_sub oc_b30 2805"
  by (oc_eval oc_c30_2805)

lemma oc_c30_2806: "oc_sub oc_b30 2806"
  by (oc_eval oc_c30_2806)

lemma oc_c30_2807: "oc_sub oc_b30 2807"
  by (oc_eval oc_c30_2807)

lemma oc_c30_2808: "oc_sub oc_b30 2808"
  by (oc_eval oc_c30_2808)

lemma oc_c30_2809: "oc_sub oc_b30 2809"
  by (oc_eval oc_c30_2809)

lemma oc_c30_2810: "oc_sub oc_b30 2810"
  by (oc_eval oc_c30_2810)

lemma oc_c30_2811: "oc_sub oc_b30 2811"
  by (oc_eval oc_c30_2811)

lemma oc_c30_2812: "oc_sub oc_b30 2812"
  by (oc_eval oc_c30_2812)

lemma oc_c30_2813: "oc_sub oc_b30 2813"
  by (oc_eval oc_c30_2813)

lemma oc_c30_2814: "oc_sub oc_b30 2814"
  by (oc_eval oc_c30_2814)

lemma oc_c30_2815: "oc_sub oc_b30 2815"
  by (oc_eval oc_c30_2815)

lemma upt_c30_175: "[2800..<2816] = [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]"
  by (simp add: upt_rec)

lemma sec_c30_175: "\<forall>j\<in>{16 * 175..<16 * 175 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 175..<16 * 175 + 16}"
  then have "j \<in> set [2800..<2816]" unfolding set_upt by simp
  then have "j \<in> set [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]" unfolding upt_c30_175 .
  then show "oc_sub oc_b30 j" using oc_c30_2800 oc_c30_2801 oc_c30_2802 oc_c30_2803 oc_c30_2804 oc_c30_2805 oc_c30_2806 oc_c30_2807 oc_c30_2808 oc_c30_2809 oc_c30_2810 oc_c30_2811 oc_c30_2812 oc_c30_2813 oc_c30_2814 oc_c30_2815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
