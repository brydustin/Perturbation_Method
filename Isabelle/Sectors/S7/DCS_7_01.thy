theory DCS_7_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_116: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 116) (-8)) (Float (int 116 + 1) (-8))"
  by eval

lemma dc_nc_116: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 116) (-8)) (Float (int 116 + 1) (-8))"
  by eval

lemma dc_c30_117: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 117) (-8)) (Float (int 117 + 1) (-8))"
  by eval

lemma dc_nc_117: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 117) (-8)) (Float (int 117 + 1) (-8))"
  by eval

lemma dc_c30_118: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 118) (-8)) (Float (int 118 + 1) (-8))"
  by eval

lemma dc_nc_118: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 118) (-8)) (Float (int 118 + 1) (-8))"
  by eval

lemma dc_c30_119: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 119) (-8)) (Float (int 119 + 1) (-8))"
  by eval

lemma dc_nc_119: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 119) (-8)) (Float (int 119 + 1) (-8))"
  by eval

end
