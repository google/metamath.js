

axiom df-ov
  let hal: type al
  let hbe: type be
  let hga: type ga
  let ta: term A
  let tb: term B
  let tf: term F
  assume wov.1: |- F : ( al -> ( be -> ga ) )
  assume wov.2: |- A : al
  assume wov.3: |- B : be
  assert |- T. |= ( ( = [ A F B ] ) ( ( F A ) B ) )
end
