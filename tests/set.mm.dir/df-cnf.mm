
axiom df-cnf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  assert |- CNF = ( x e. On , y e. On |-> ( f e. { g e. ( x ^m y ) | g finSupp (/) } |-> [_ OrdIso ( _E , ( f supp (/) ) ) / h ]_ ( seqom ( ( k e. _V , z e. _V |-> ( ( ( x ^o ( h ` k ) ) .o ( f ` ( h ` k ) ) ) +o z ) ) , (/) ) ` dom h ) ) )
end
