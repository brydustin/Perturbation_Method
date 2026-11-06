theory DCS_6_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_108: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 108) (-8)) (Float (int 108 + 1) (-8))"
  by eval

lemma dc_nc_108: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 108) (-8)) (Float (int 108 + 1) (-8))"
  by eval

lemma dc_c30_109: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 109) (-8)) (Float (int 109 + 1) (-8))"
  by eval

lemma dc_nc_109: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 109) (-8)) (Float (int 109 + 1) (-8))"
  by eval

lemma dc_c30_110: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 110) (-8)) (Float (int 110 + 1) (-8))"
  by eval

lemma dc_nc_110: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 110) (-8)) (Float (int 110 + 1) (-8))"
  by eval

lemma dc_c30_111: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 111) (-8)) (Float (int 111 + 1) (-8))"
  by eval

lemma dc_nc_111: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 111) (-8)) (Float (int 111 + 1) (-8))"
  by eval

end
