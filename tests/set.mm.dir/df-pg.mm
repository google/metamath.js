
axiom df-pg
  let vx: setvar x
  assert |- Pg = setrecs ( ( x e. _V |-> ( ~P x X. ~P x ) ) )
end
