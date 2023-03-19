

axiom df-ov
  param hal: type al
  param hbe: type be
  param hga: type ga
  param ta: term A
  param tb: term B
  param tf: term F
  assume wov.1: |- F : ( al -> ( be -> ga ) )
  assume wov.2: |- A : al
  assume wov.3: |- B : be
  assert |- T. |= ( ( = [ A F B ] ) ( ( F A ) B ) )
end
