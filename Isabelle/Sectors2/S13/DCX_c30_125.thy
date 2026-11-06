theory DCX_c30_125
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2000: "dc_sub dc_b30 2000"
  by (dc_eval dc_c30_2000)

lemma dc_c30_2001: "dc_sub dc_b30 2001"
  by (dc_eval dc_c30_2001)

lemma dc_c30_2002: "dc_sub dc_b30 2002"
  by (dc_eval dc_c30_2002)

lemma dc_c30_2003: "dc_sub dc_b30 2003"
  by (dc_eval dc_c30_2003)

lemma dc_c30_2004: "dc_sub dc_b30 2004"
  by (dc_eval dc_c30_2004)

lemma dc_c30_2005: "dc_sub dc_b30 2005"
  by (dc_eval dc_c30_2005)

lemma dc_c30_2006: "dc_sub dc_b30 2006"
  by (dc_eval dc_c30_2006)

lemma dc_c30_2007: "dc_sub dc_b30 2007"
  by (dc_eval dc_c30_2007)

lemma dc_c30_2008: "dc_sub dc_b30 2008"
  by (dc_eval dc_c30_2008)

lemma dc_c30_2009: "dc_sub dc_b30 2009"
  by (dc_eval dc_c30_2009)

lemma dc_c30_2010: "dc_sub dc_b30 2010"
  by (dc_eval dc_c30_2010)

lemma dc_c30_2011: "dc_sub dc_b30 2011"
  by (dc_eval dc_c30_2011)

lemma dc_c30_2012: "dc_sub dc_b30 2012"
  by (dc_eval dc_c30_2012)

lemma dc_c30_2013: "dc_sub dc_b30 2013"
  by (dc_eval dc_c30_2013)

lemma dc_c30_2014: "dc_sub dc_b30 2014"
  by (dc_eval dc_c30_2014)

lemma dc_c30_2015: "dc_sub dc_b30 2015"
  by (dc_eval dc_c30_2015)

lemma upt_c30_125: "[2000..<2016] = [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]"
  by (simp add: upt_rec)

lemma sec_c30_125: "\<forall>j\<in>{16 * 125..<16 * 125 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 125..<16 * 125 + 16}"
  then have "j \<in> set [2000..<2016]" unfolding set_upt by simp
  then have "j \<in> set [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]" unfolding upt_c30_125 .
  then show "dc_sub dc_b30 j" using dc_c30_2000 dc_c30_2001 dc_c30_2002 dc_c30_2003 dc_c30_2004 dc_c30_2005 dc_c30_2006 dc_c30_2007 dc_c30_2008 dc_c30_2009 dc_c30_2010 dc_c30_2011 dc_c30_2012 dc_c30_2013 dc_c30_2014 dc_c30_2015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
