
axiom df-ushgr
  let vv: setvar v
  let ve: setvar e
  let vg: setvar g
  assert |- USHGraph = { g | [. ( Vtx ` g ) / v ]. [. ( iEdg ` g ) / e ]. e : dom e -1-1-> ( ~P v \ { (/) } ) }
end
