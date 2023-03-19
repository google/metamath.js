include "comi31.mm"

theorem u3lemc5
  let wva: term a
  let wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( a ->3 b )

  proof
    wva
    wvb
    comi31
end
