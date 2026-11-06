theory GDCX_nc_175
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2800: "gdc_sub None 2800"
  by (gdc_eval gdc_nc_2800)

lemma gdc_nc_2801: "gdc_sub None 2801"
  by (gdc_eval gdc_nc_2801)

lemma gdc_nc_2802: "gdc_sub None 2802"
  by (gdc_eval gdc_nc_2802)

lemma gdc_nc_2803: "gdc_sub None 2803"
  by (gdc_eval gdc_nc_2803)

lemma gdc_nc_2804: "gdc_sub None 2804"
  by (gdc_eval gdc_nc_2804)

lemma gdc_nc_2805: "gdc_sub None 2805"
  by (gdc_eval gdc_nc_2805)

lemma gdc_nc_2806: "gdc_sub None 2806"
  by (gdc_eval gdc_nc_2806)

lemma gdc_nc_2807: "gdc_sub None 2807"
  by (gdc_eval gdc_nc_2807)

lemma gdc_nc_2808: "gdc_sub None 2808"
  by (gdc_eval gdc_nc_2808)

lemma gdc_nc_2809: "gdc_sub None 2809"
  by (gdc_eval gdc_nc_2809)

lemma gdc_nc_2810: "gdc_sub None 2810"
  by (gdc_eval gdc_nc_2810)

lemma gdc_nc_2811: "gdc_sub None 2811"
  by (gdc_eval gdc_nc_2811)

lemma gdc_nc_2812: "gdc_sub None 2812"
  by (gdc_eval gdc_nc_2812)

lemma gdc_nc_2813: "gdc_sub None 2813"
  by (gdc_eval gdc_nc_2813)

lemma gdc_nc_2814: "gdc_sub None 2814"
  by (gdc_eval gdc_nc_2814)

lemma gdc_nc_2815: "gdc_sub None 2815"
  by (gdc_eval gdc_nc_2815)

lemma gupt_nc_175: "[2800..<2816] = [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]"
  by (simp add: upt_rec)

lemma gsec_nc_175: "\<forall>j\<in>{16 * 175..<16 * 175 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 175..<16 * 175 + 16}"
  then have "j \<in> set [2800..<2816]" unfolding set_upt by simp
  then have "j \<in> set [2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815]" unfolding gupt_nc_175 .
  then show "gdc_sub None j" using gdc_nc_2800 gdc_nc_2801 gdc_nc_2802 gdc_nc_2803 gdc_nc_2804 gdc_nc_2805 gdc_nc_2806 gdc_nc_2807 gdc_nc_2808 gdc_nc_2809 gdc_nc_2810 gdc_nc_2811 gdc_nc_2812 gdc_nc_2813 gdc_nc_2814 gdc_nc_2815
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
