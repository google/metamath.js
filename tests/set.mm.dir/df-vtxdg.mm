
axiom df-vtxdg
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let ve: setvar e
  let vg: setvar g
  assert |- VtxDeg = ( g e. _V |-> [_ ( Vtx ` g ) / v ]_ [_ ( iEdg ` g ) / e ]_ ( u e. v |-> ( ( # ` { x e. dom e | u e. ( e ` x ) } ) +e ( # ` { x e. dom e | ( e ` x ) = { u } } ) ) ) )
end
