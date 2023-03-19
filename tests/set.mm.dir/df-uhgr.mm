
axiom df-uhgr
  let vv: setvar v
  let ve: setvar e
  let vg: setvar g
  assert |- UHGraph = { g | [. ( Vtx ` g ) / v ]. [. ( iEdg ` g ) / e ]. e : dom e --> ( ~P v \ { (/) } ) }
end
