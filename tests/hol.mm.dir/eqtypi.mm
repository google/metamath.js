

axiom eqtypi
  param hal: type al
  param ta: term A
  param tb: term B
  param tr: term R
  assume eqcomi.1: |- A : al
  assume eqcomi.2: |- R |= [ A = B ]
  assert |- B : al
end
