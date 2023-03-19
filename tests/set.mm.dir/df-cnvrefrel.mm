
axiom df-cnvrefrel
  let cR: class R
  assert |- ( CnvRefRel R <-> ( ( R i^i ( dom R X. ran R ) ) C_ ( _I i^i ( dom R X. ran R ) ) /\ Rel R ) )
end
