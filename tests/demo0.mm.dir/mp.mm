
axiom mp
  let wp: wff P
  let wq: wff Q
  assume min: |- P
  assume maj: |- ( P -> Q )
  assert |- Q
end
