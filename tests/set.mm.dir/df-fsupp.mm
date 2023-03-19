
axiom df-fsupp
  let vz: setvar z
  let vr: setvar r
  assert |- finSupp = { <. r , z >. | ( Fun r /\ ( r supp z ) e. Fin ) }
end
