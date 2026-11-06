theory DCS_11_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_176: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 176) (-8)) (Float (int 176 + 1) (-8))"
  by eval

lemma dc_nc_176: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 176) (-8)) (Float (int 176 + 1) (-8))"
  by eval

lemma dc_c30_177: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 177) (-8)) (Float (int 177 + 1) (-8))"
  by eval

lemma dc_nc_177: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 177) (-8)) (Float (int 177 + 1) (-8))"
  by eval

lemma dc_c30_178: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 178) (-8)) (Float (int 178 + 1) (-8))"
  by eval

lemma dc_nc_178: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 178) (-8)) (Float (int 178 + 1) (-8))"
  by eval

lemma dc_c30_179: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 179) (-8)) (Float (int 179 + 1) (-8))"
  by eval

lemma dc_nc_179: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 179) (-8)) (Float (int 179 + 1) (-8))"
  by eval

end
