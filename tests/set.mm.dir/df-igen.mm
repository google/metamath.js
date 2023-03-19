
axiom df-igen
  let vj: setvar j
  let vs: setvar s
  let vr: setvar r
  assert |- IdlGen = ( r e. RingOps , s e. ~P ran ( 1st ` r ) |-> |^| { j e. ( Idl ` r ) | s C_ j } )
end
