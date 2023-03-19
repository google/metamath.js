
axiom df-ac
  let vx: setvar x
  let vf: setvar f
  assert |- ( CHOICE <-> A. x E. f ( f C_ x /\ f Fn dom x ) )
end
