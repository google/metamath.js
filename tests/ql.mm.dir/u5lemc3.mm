include "u5lemc1b.mm"

theorem u5lemc3
  let wva: term a
  let wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( b ->5 a )

  proof
    wvb
    wva
    u5lemc1b
end
