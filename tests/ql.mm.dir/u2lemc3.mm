include "u2lemc1.mm"

theorem u2lemc3
  let wva: term a
  let wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( b ->2 a )

  proof
    wvb
    wva
    u2lemc1
end
