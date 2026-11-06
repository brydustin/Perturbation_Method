theory GDCX_nc_116
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1856: "gdc_sub None 1856"
  by (gdc_eval gdc_nc_1856)

lemma gdc_nc_1857: "gdc_sub None 1857"
  by (gdc_eval gdc_nc_1857)

lemma gdc_nc_1858: "gdc_sub None 1858"
  by (gdc_eval gdc_nc_1858)

lemma gdc_nc_1859: "gdc_sub None 1859"
  by (gdc_eval gdc_nc_1859)

lemma gdc_nc_1860: "gdc_sub None 1860"
  by (gdc_eval gdc_nc_1860)

lemma gdc_nc_1861: "gdc_sub None 1861"
  by (gdc_eval gdc_nc_1861)

lemma gdc_nc_1862: "gdc_sub None 1862"
  by (gdc_eval gdc_nc_1862)

lemma gdc_nc_1863: "gdc_sub None 1863"
  by (gdc_eval gdc_nc_1863)

lemma gdc_nc_1864: "gdc_sub None 1864"
  by (gdc_eval gdc_nc_1864)

lemma gdc_nc_1865: "gdc_sub None 1865"
  by (gdc_eval gdc_nc_1865)

lemma gdc_nc_1866: "gdc_sub None 1866"
  by (gdc_eval gdc_nc_1866)

lemma gdc_nc_1867: "gdc_sub None 1867"
  by (gdc_eval gdc_nc_1867)

lemma gdc_nc_1868: "gdc_sub None 1868"
  by (gdc_eval gdc_nc_1868)

lemma gdc_nc_1869: "gdc_sub None 1869"
  by (gdc_eval gdc_nc_1869)

lemma gdc_nc_1870: "gdc_sub None 1870"
  by (gdc_eval gdc_nc_1870)

lemma gdc_nc_1871: "gdc_sub None 1871"
  by (gdc_eval gdc_nc_1871)

lemma gupt_nc_116: "[1856..<1872] = [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]"
  by (simp add: upt_rec)

lemma gsec_nc_116: "\<forall>j\<in>{16 * 116..<16 * 116 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 116..<16 * 116 + 16}"
  then have "j \<in> set [1856..<1872]" unfolding set_upt by simp
  then have "j \<in> set [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]" unfolding gupt_nc_116 .
  then show "gdc_sub None j" using gdc_nc_1856 gdc_nc_1857 gdc_nc_1858 gdc_nc_1859 gdc_nc_1860 gdc_nc_1861 gdc_nc_1862 gdc_nc_1863 gdc_nc_1864 gdc_nc_1865 gdc_nc_1866 gdc_nc_1867 gdc_nc_1868 gdc_nc_1869 gdc_nc_1870 gdc_nc_1871
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
