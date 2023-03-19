
axiom mp
  param wp: wff P
  param wq: wff Q
  assume min: |- P
  assume maj: |- ( P -> Q )
  assert |- Q
end
