include "eqcomi.mm"
include "eqtypi.mm"
include "3eqtr4i.mm"

theorem 3eqtr3i
  param hal: type al
  param ta: term A
  param tb: term B
  param tr: term R
  param ts: term S
  param tt: term T
  assume 3eqtr4i.1: |- A : al
  assume 3eqtr4i.2: |- R |= [ A = B ]
  assume 3eqtr3i.3: |- R |= [ A = S ]
  assume 3eqtr3i.4: |- R |= [ B = T ]


  assert |- R |= [ S = T ]

  proof
    hal
    ta
    tb
    tr
    ts
    tt
    3eqtr4i.1
    3eqtr4i.2
    hal
    ta
    ts
    tr
    3eqtr4i.1
    3eqtr3i.3
    eqcomi
    hal
    tb
    tt
    tr
    hal
    ta
    tb
    tr
    3eqtr4i.1
    3eqtr4i.2
    eqtypi
    3eqtr3i.4
    eqcomi
    3eqtr4i
end
