
axiom df-pellfund
  let vx: setvar x
  let vz: setvar z
  assert |- PellFund = ( x e. ( NN \ []NN ) |-> inf ( { z e. ( Pell14QR ` x ) | 1 < z } , RR , < ) )
end
