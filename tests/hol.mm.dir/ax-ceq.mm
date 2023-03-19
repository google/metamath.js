

axiom ax-ceq
  let hal: type al
  let hbe: type be
  let ta: term A
  let tb: term B
  let tf: term F
  let tt: term T
  assume ax-ceq.1: |- F : ( al -> be )
  assume ax-ceq.2: |- T : ( al -> be )
  assume ax-ceq.3: |- A : al
  assume ax-ceq.4: |- B : al
  assert |- ( ( ( = F ) T ) , ( ( = A ) B ) ) |= ( ( = ( F A ) ) ( T B ) )
end
