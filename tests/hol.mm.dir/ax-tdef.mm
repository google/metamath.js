
axiom ax-tdef
  param hal: type al
  param hbe: type be
  param vx: var x
  param ta: term A
  param tb: term B
  param tf: term F
  param tr: term R
  assume ax-tdef.1: |- B : al
  assume ax-tdef.2: |- F : ( al -> bool )
  assume ax-tdef.3: |- T. |= ( F B )
  assume ax-tdef.4: |- typedef be ( A , R ) F
  assert |- T. |= ( ( ! \ x : be . [ ( A ( R x : be ) ) = x : be ] ) , ( ! \ x : al . [ ( F x : al ) = [ ( R ( A x : al ) ) = x : al ] ] ) )
end
