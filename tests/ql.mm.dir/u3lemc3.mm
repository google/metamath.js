include "comi32.mm"

theorem u3lemc3
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( b ->3 a )

  proof
    wva
    wvb
    ulemc3.1
    comi32
end
