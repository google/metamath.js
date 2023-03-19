
axiom df-usgr
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let vg: setvar g
  assert |- USGraph = { g | [. ( Vtx ` g ) / v ]. [. ( iEdg ` g ) / e ]. e : dom e -1-1-> { x e. ( ~P v \ { (/) } ) | ( # ` x ) = 2 } }
end
