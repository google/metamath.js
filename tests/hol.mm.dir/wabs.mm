
axiom wabs
  param hal: type al
  param hbe: type be
  param ta: term A
  param tb: term B
  param tf: term F
  param tr: term R
  assume ax-tdef.1: |- B : al
  assume ax-tdef.2: |- F : ( al -> bool )
  assume ax-tdef.3: |- T. |= ( F B )
  assume ax-tdef.4: |- typedef be ( A , R ) F
  assert |- A : ( al -> be )
end
