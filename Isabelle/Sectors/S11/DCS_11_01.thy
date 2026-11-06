theory DCS_11_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_180: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 180) (-8)) (Float (int 180 + 1) (-8))"
  by eval

lemma dc_nc_180: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 180) (-8)) (Float (int 180 + 1) (-8))"
  by eval

lemma dc_c30_181: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 181) (-8)) (Float (int 181 + 1) (-8))"
  by eval

lemma dc_nc_181: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 181) (-8)) (Float (int 181 + 1) (-8))"
  by eval

lemma dc_c30_182: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 182) (-8)) (Float (int 182 + 1) (-8))"
  by eval

lemma dc_nc_182: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 182) (-8)) (Float (int 182 + 1) (-8))"
  by eval

lemma dc_c30_183: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 183) (-8)) (Float (int 183 + 1) (-8))"
  by eval

lemma dc_nc_183: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 183) (-8)) (Float (int 183 + 1) (-8))"
  by eval

end
