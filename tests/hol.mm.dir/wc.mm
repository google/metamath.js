
axiom wc
  let hal: type al
  let hbe: type be
  let tf: term F
  let tt: term T
  assume wc.1: |- F : ( al -> be )
  assume wc.2: |- T : al
  assert |- ( F T ) : be
end
