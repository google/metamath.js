
axiom df-drngo
  let vg: setvar g
  let vh: setvar h
  assert |- DivRingOps = { <. g , h >. | ( <. g , h >. e. RingOps /\ ( h |` ( ( ran g \ { ( GId ` g ) } ) X. ( ran g \ { ( GId ` g ) } ) ) ) e. GrpOp ) }
end
