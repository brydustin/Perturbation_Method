theory OCX_nc_175
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2800: "oc_sub None 2800"
  by (oc_eval oc_nc_2800)

lemma oc_nc_2801: "oc_sub None 2801"
  by (oc_eval oc_nc_2801)

lemma oc_nc_2802: "oc_sub None 2802"
  by (oc_eval oc_nc_2802)

lemma oc_nc_2803: "oc_sub None 2803"
  by (oc_eval oc_nc_2803)

lemma oc_nc_2804: "oc_sub None 2804"
  by (oc_eval oc_nc_2804)

lemma oc_nc_2805: "oc_sub None 2805"
  by (oc_eval oc_nc_2805)

lemma oc_nc_2806: "oc_sub None 2806"
  by (oc_eval oc_nc_2806)

lemma oc_nc_2807: "oc_sub None 2807"
  by (oc_eval oc_nc_2807)

lemma oc_nc_2808: "oc_sub None 2808"
  by (oc_eval oc_nc_2808)

lemma oc_nc_2809: "oc_sub None 2809"
  by (oc_eval oc_nc_2809)

lemma oc_nc_2810: "oc_sub None 2810"
  by (oc_eval oc_nc_2810)

lemma oc_nc_2811: "oc_sub None 2811"
  by (oc_eval oc_nc_2811)

lemma oc_nc_2812: "oc_sub None 2812"
  by (oc_eval oc_nc_2812)

lemma oc_nc_2813: "oc_sub None 2813"
  by (oc_eval oc_nc_2813)

lemma oc_nc_2814: "oc_sub None 2814"
  by (oc_eval oc_nc_2814)

lemma oc_nc_2815: "oc_sub None 2815"
  by (oc_eval oc_nc_2815)

lemma upt_nc_175: "[2800..<2816] = [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]"
  by (simp add: upt_rec)

lemma sec_nc_175: "\<forall>j\<in>{16 * 175..<16 * 175 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 175..<16 * 175 + 16}"
  then have "j \<in> set [2800..<2816]" unfolding set_upt by simp
  then have "j \<in> set [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]" unfolding upt_nc_175 .
  then show "oc_sub None j" using oc_nc_2800 oc_nc_2801 oc_nc_2802 oc_nc_2803 oc_nc_2804 oc_nc_2805 oc_nc_2806 oc_nc_2807 oc_nc_2808 oc_nc_2809 oc_nc_2810 oc_nc_2811 oc_nc_2812 oc_nc_2813 oc_nc_2814 oc_nc_2815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
