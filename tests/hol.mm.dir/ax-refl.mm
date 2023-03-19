

axiom ax-refl
  param hal: type al
  param ta: term A
  assume ax-refl.1: |- A : al
  assert |- T. |= ( ( = A ) A )
end
