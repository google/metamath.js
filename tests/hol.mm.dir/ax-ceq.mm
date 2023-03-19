

axiom ax-ceq
  param hal: type al
  param hbe: type be
  param ta: term A
  param tb: term B
  param tf: term F
  param tt: term T
  assume ax-ceq.1: |- F : ( al -> be )
  assume ax-ceq.2: |- T : ( al -> be )
  assume ax-ceq.3: |- A : al
  assume ax-ceq.4: |- B : al
  assert |- ( ( ( = F ) T ) , ( ( = A ) B ) ) |= ( ( = ( F A ) ) ( T B ) )
end
