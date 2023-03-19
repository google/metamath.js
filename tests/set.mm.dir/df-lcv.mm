
axiom df-lcv
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let vs: setvar s
  assert |- <oL = ( w e. _V |-> { <. t , u >. | ( ( t e. ( LSubSp ` w ) /\ u e. ( LSubSp ` w ) ) /\ ( t C. u /\ -. E. s e. ( LSubSp ` w ) ( t C. s /\ s C. u ) ) ) } )
end
