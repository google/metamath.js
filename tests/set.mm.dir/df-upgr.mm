
axiom df-upgr
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let vg: setvar g
  assert |- UPGraph = { g | [. ( Vtx ` g ) / v ]. [. ( iEdg ` g ) / e ]. e : dom e --> { x e. ( ~P v \ { (/) } ) | ( # ` x ) <_ 2 } }
end
