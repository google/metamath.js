
axiom df-risc
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- ~=R = { <. r , s >. | ( ( r e. RingOps /\ s e. RingOps ) /\ E. f f e. ( r RngIso s ) ) }
end
