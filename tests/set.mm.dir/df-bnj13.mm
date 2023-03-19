
axiom df-bnj13
  let vx: setvar x
  let cA: class A
  let cR: class R
  assert |- ( R _Se A <-> A. x e. A _pred ( x , A , R ) e. _V )
end
