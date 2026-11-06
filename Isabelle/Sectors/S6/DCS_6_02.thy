theory DCS_6_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_104: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 104) (-8)) (Float (int 104 + 1) (-8))"
  by eval

lemma dc_nc_104: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 104) (-8)) (Float (int 104 + 1) (-8))"
  by eval

lemma dc_c30_105: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 105) (-8)) (Float (int 105 + 1) (-8))"
  by eval

lemma dc_nc_105: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 105) (-8)) (Float (int 105 + 1) (-8))"
  by eval

lemma dc_c30_106: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 106) (-8)) (Float (int 106 + 1) (-8))"
  by eval

lemma dc_nc_106: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 106) (-8)) (Float (int 106 + 1) (-8))"
  by eval

lemma dc_c30_107: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 107) (-8)) (Float (int 107 + 1) (-8))"
  by eval

lemma dc_nc_107: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 107) (-8)) (Float (int 107 + 1) (-8))"
  by eval

end
