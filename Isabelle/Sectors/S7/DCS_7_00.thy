theory DCS_7_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_112: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 112) (-8)) (Float (int 112 + 1) (-8))"
  by eval

lemma dc_nc_112: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 112) (-8)) (Float (int 112 + 1) (-8))"
  by eval

lemma dc_c30_113: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 113) (-8)) (Float (int 113 + 1) (-8))"
  by eval

lemma dc_nc_113: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 113) (-8)) (Float (int 113 + 1) (-8))"
  by eval

lemma dc_c30_114: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 114) (-8)) (Float (int 114 + 1) (-8))"
  by eval

lemma dc_nc_114: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 114) (-8)) (Float (int 114 + 1) (-8))"
  by eval

lemma dc_c30_115: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 115) (-8)) (Float (int 115 + 1) (-8))"
  by eval

lemma dc_nc_115: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 115) (-8)) (Float (int 115 + 1) (-8))"
  by eval

end
