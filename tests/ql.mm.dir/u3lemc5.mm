include "comi31.mm"

theorem u3lemc5
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( a ->3 b )

  proof
    wva
    wvb
    comi31
end
