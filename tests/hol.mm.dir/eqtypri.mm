
axiom eqtypri
  let hal: type al
  let ta: term A
  let tb: term B
  let tr: term R
  assume eqtypri.1: |- A : al
  assume eqtypri.2: |- R |= [ B = A ]
  assert |- B : al
end
