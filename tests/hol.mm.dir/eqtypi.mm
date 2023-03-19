
axiom eqtypi
  let hal: type al
  let ta: term A
  let tb: term B
  let tr: term R
  assume eqcomi.1: |- A : al
  assume eqcomi.2: |- R |= [ A = B ]
  assert |- B : al
end
