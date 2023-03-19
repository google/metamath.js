include "eqcomi.mm"
include "eqtypi.mm"
include "3eqtr4i.mm"

theorem 3eqtr3i
  let hal: type al
  let ta: term A
  let tb: term B
  let tr: term R
  let ts: term S
  let tt: term T
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
