

axiom wc
  param hal: type al
  param hbe: type be
  param tf: term F
  param tt: term T
  assume wc.1: |- F : ( al -> be )
  assume wc.2: |- T : al
  assert |- ( F T ) : be
end
