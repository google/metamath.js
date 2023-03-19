include "u5lemc1b.mm"

theorem u5lemc3
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( b ->5 a )

  proof
    wvb
    wva
    u5lemc1b
end
