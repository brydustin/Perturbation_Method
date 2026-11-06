theory DCX_nc_116
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1856: "dc_sub None 1856"
  by (dc_eval dc_nc_1856)

lemma dc_nc_1857: "dc_sub None 1857"
  by (dc_eval dc_nc_1857)

lemma dc_nc_1858: "dc_sub None 1858"
  by (dc_eval dc_nc_1858)

lemma dc_nc_1859: "dc_sub None 1859"
  by (dc_eval dc_nc_1859)

lemma dc_nc_1860: "dc_sub None 1860"
  by (dc_eval dc_nc_1860)

lemma dc_nc_1861: "dc_sub None 1861"
  by (dc_eval dc_nc_1861)

lemma dc_nc_1862: "dc_sub None 1862"
  by (dc_eval dc_nc_1862)

lemma dc_nc_1863: "dc_sub None 1863"
  by (dc_eval dc_nc_1863)

lemma dc_nc_1864: "dc_sub None 1864"
  by (dc_eval dc_nc_1864)

lemma dc_nc_1865: "dc_sub None 1865"
  by (dc_eval dc_nc_1865)

lemma dc_nc_1866: "dc_sub None 1866"
  by (dc_eval dc_nc_1866)

lemma dc_nc_1867: "dc_sub None 1867"
  by (dc_eval dc_nc_1867)

lemma dc_nc_1868: "dc_sub None 1868"
  by (dc_eval dc_nc_1868)

lemma dc_nc_1869: "dc_sub None 1869"
  by (dc_eval dc_nc_1869)

lemma dc_nc_1870: "dc_sub None 1870"
  by (dc_eval dc_nc_1870)

lemma dc_nc_1871: "dc_sub None 1871"
  by (dc_eval dc_nc_1871)

lemma upt_nc_116: "[1856..<1872] = [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]"
  by (simp add: upt_rec)

lemma sec_nc_116: "\<forall>j\<in>{16 * 116..<16 * 116 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 116..<16 * 116 + 16}"
  then have "j \<in> set [1856..<1872]" unfolding set_upt by simp
  then have "j \<in> set [1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871]" unfolding upt_nc_116 .
  then show "dc_sub None j" using dc_nc_1856 dc_nc_1857 dc_nc_1858 dc_nc_1859 dc_nc_1860 dc_nc_1861 dc_nc_1862 dc_nc_1863 dc_nc_1864 dc_nc_1865 dc_nc_1866 dc_nc_1867 dc_nc_1868 dc_nc_1869 dc_nc_1870 dc_nc_1871
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
