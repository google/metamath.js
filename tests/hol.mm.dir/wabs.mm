
axiom wabs
  let hal: type al
  let hbe: type be
  let ta: term A
  let tb: term B
  let tf: term F
  let tr: term R
  assume ax-tdef.1: |- B : al
  assume ax-tdef.2: |- F : ( al -> bool )
  assume ax-tdef.3: |- T. |= ( F B )
  assume ax-tdef.4: |- typedef be ( A , R ) F
  assert |- A : ( al -> be )
end
