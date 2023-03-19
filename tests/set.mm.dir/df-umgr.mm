
axiom df-umgr
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let vg: setvar g
  assert |- UMGraph = { g | [. ( Vtx ` g ) / v ]. [. ( iEdg ` g ) / e ]. e : dom e --> { x e. ( ~P v \ { (/) } ) | ( # ` x ) = 2 } }
end
