
axiom df-gid
  let vx: setvar x
  let vu: setvar u
  let vg: setvar g
  assert |- GId = ( g e. _V |-> ( iota_ u e. ran g A. x e. ran g ( ( u g x ) = x /\ ( x g u ) = x ) ) )
end
