
axiom df-prv
  let vu: setvar u
  let vm: setvar m
  assert |- |= = { <. m , u >. | ( m SatE u ) = ( m ^m _om ) }
end
