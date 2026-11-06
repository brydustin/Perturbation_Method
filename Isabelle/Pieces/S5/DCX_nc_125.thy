theory DCX_nc_125
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2000: "dc_sub None 2000"
  by (dc_eval dc_nc_2000)

lemma dc_nc_2001: "dc_sub None 2001"
  by (dc_eval dc_nc_2001)

lemma dc_nc_2002: "dc_sub None 2002"
  by (dc_eval dc_nc_2002)

lemma dc_nc_2003: "dc_sub None 2003"
  by (dc_eval dc_nc_2003)

lemma dc_nc_2004: "dc_sub None 2004"
  by (dc_eval dc_nc_2004)

lemma dc_nc_2005: "dc_sub None 2005"
  by (dc_eval dc_nc_2005)

lemma dc_nc_2006: "dc_sub None 2006"
  by (dc_eval dc_nc_2006)

lemma dc_nc_2007: "dc_sub None 2007"
  by (dc_eval dc_nc_2007)

lemma dc_nc_2008: "dc_sub None 2008"
  by (dc_eval dc_nc_2008)

lemma dc_nc_2009: "dc_sub None 2009"
  by (dc_eval dc_nc_2009)

lemma dc_nc_2010: "dc_sub None 2010"
  by (dc_eval dc_nc_2010)

lemma dc_nc_2011: "dc_sub None 2011"
  by (dc_eval dc_nc_2011)

lemma dc_nc_2012: "dc_sub None 2012"
  by (dc_eval dc_nc_2012)

lemma dc_nc_2013: "dc_sub None 2013"
  by (dc_eval dc_nc_2013)

lemma dc_nc_2014: "dc_sub None 2014"
  by (dc_eval dc_nc_2014)

lemma dc_nc_2015: "dc_sub None 2015"
  by (dc_eval dc_nc_2015)

lemma upt_nc_125: "[2000..<2016] = [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]"
  by (simp add: upt_rec)

lemma sec_nc_125: "\<forall>j\<in>{16 * 125..<16 * 125 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 125..<16 * 125 + 16}"
  then have "j \<in> set [2000..<2016]" unfolding set_upt by simp
  then have "j \<in> set [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]" unfolding upt_nc_125 .
  then show "dc_sub None j" using dc_nc_2000 dc_nc_2001 dc_nc_2002 dc_nc_2003 dc_nc_2004 dc_nc_2005 dc_nc_2006 dc_nc_2007 dc_nc_2008 dc_nc_2009 dc_nc_2010 dc_nc_2011 dc_nc_2012 dc_nc_2013 dc_nc_2014 dc_nc_2015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
