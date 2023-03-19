
axiom df-blo
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  assert |- BLnOp = ( u e. NrmCVec , w e. NrmCVec |-> { t e. ( u LnOp w ) | ( ( u normOpOLD w ) ` t ) < +oo } )
end
