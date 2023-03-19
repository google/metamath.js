include "com2i3.mm"

theorem u3lemc2
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume ulemc2.1: |- a C b
  assume ulemc2.2: |- a C c


  assert |- a C ( b ->3 c )

  proof
    wva
    wvb
    wvc
    ulemc2.1
    ulemc2.2
    com2i3
end
