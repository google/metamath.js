include "u4lemc1.mm"

theorem u4lemc3
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( b ->4 a )

  proof
    wvb
    wva
    u4lemc1
end
