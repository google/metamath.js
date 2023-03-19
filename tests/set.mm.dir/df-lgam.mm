
axiom df-lgam
  let vz: setvar z
  let vm: setvar m
  assert |- log_G = ( z e. ( CC \ ( ZZ \ NN ) ) |-> ( sum_ m e. NN ( ( z x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( z / m ) + 1 ) ) ) - ( log ` z ) ) )
end
