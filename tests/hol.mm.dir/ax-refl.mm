
axiom ax-refl
  let hal: type al
  let ta: term A
  assume ax-refl.1: |- A : al
  assert |- T. |= ( ( = A ) A )
end
