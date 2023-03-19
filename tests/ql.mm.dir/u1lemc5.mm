include "u1lemc1.mm"

theorem u1lemc5
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( a ->1 b )

  proof
    wva
    wvb
    u1lemc1
end
