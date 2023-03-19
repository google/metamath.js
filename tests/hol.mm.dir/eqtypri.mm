

axiom eqtypri
  param hal: type al
  param ta: term A
  param tb: term B
  param tr: term R
  assume eqtypri.1: |- A : al
  assume eqtypri.2: |- R |= [ B = A ]
  assert |- B : al
end
