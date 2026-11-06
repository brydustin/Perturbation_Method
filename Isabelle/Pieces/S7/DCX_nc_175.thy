theory DCX_nc_175
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2800: "dc_sub None 2800"
  by (dc_eval dc_nc_2800)

lemma dc_nc_2801: "dc_sub None 2801"
  by (dc_eval dc_nc_2801)

lemma dc_nc_2802: "dc_sub None 2802"
  by (dc_eval dc_nc_2802)

lemma dc_nc_2803: "dc_sub None 2803"
  by (dc_eval dc_nc_2803)

lemma dc_nc_2804: "dc_sub None 2804"
  by (dc_eval dc_nc_2804)

lemma dc_nc_2805: "dc_sub None 2805"
  by (dc_eval dc_nc_2805)

lemma dc_nc_2806: "dc_sub None 2806"
  by (dc_eval dc_nc_2806)

lemma dc_nc_2807: "dc_sub None 2807"
  by (dc_eval dc_nc_2807)

lemma dc_nc_2808: "dc_sub None 2808"
  by (dc_eval dc_nc_2808)

lemma dc_nc_2809: "dc_sub None 2809"
  by (dc_eval dc_nc_2809)

lemma dc_nc_2810: "dc_sub None 2810"
  by (dc_eval dc_nc_2810)

lemma dc_nc_2811: "dc_sub None 2811"
  by (dc_eval dc_nc_2811)

lemma dc_nc_2812: "dc_sub None 2812"
  by (dc_eval dc_nc_2812)

lemma dc_nc_2813: "dc_sub None 2813"
  by (dc_eval dc_nc_2813)

lemma dc_nc_2814: "dc_sub None 2814"
  by (dc_eval dc_nc_2814)

lemma dc_nc_2815: "dc_sub None 2815"
  by (dc_eval dc_nc_2815)

lemma upt_nc_175: "[2800..<2816] = [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]"
  by (simp add: upt_rec)

lemma sec_nc_175: "\<forall>j\<in>{16 * 175..<16 * 175 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 175..<16 * 175 + 16}"
  then have "j \<in> set [2800..<2816]" unfolding set_upt by simp
  then have "j \<in> set [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]" unfolding upt_nc_175 .
  then show "dc_sub None j" using dc_nc_2800 dc_nc_2801 dc_nc_2802 dc_nc_2803 dc_nc_2804 dc_nc_2805 dc_nc_2806 dc_nc_2807 dc_nc_2808 dc_nc_2809 dc_nc_2810 dc_nc_2811 dc_nc_2812 dc_nc_2813 dc_nc_2814 dc_nc_2815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
