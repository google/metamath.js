
axiom df-seq
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cF: class F
  let cM: class M
  assert |- seq M ( .+ , F ) = ( rec ( ( x e. _V , y e. _V |-> <. ( x + 1 ) , ( y .+ ( F ` ( x + 1 ) ) ) >. ) , <. M , ( F ` M ) >. ) " _om )
end
