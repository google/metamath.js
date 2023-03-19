include "u5lemc1.mm"

theorem u5lemc5
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( a ->5 b )

  proof
    wva
    wvb
    u5lemc1
end
