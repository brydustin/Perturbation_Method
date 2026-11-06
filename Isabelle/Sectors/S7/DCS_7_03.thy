theory DCS_7_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_124: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 124) (-8)) (Float (int 124 + 1) (-8))"
  by eval

lemma dc_nc_124: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 124) (-8)) (Float (int 124 + 1) (-8))"
  by eval

lemma dc_c30_125: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 125) (-8)) (Float (int 125 + 1) (-8))"
  by eval

lemma dc_nc_125: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 125) (-8)) (Float (int 125 + 1) (-8))"
  by eval

lemma dc_c30_126: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 126) (-8)) (Float (int 126 + 1) (-8))"
  by eval

lemma dc_nc_126: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 126) (-8)) (Float (int 126 + 1) (-8))"
  by eval

lemma dc_c30_127: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 127) (-8)) (Float (int 127 + 1) (-8))"
  by eval

lemma dc_nc_127: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 127) (-8)) (Float (int 127 + 1) (-8))"
  by eval

end
