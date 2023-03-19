include "comid.mm"
include "u4lemc2.mm"

theorem u4lemc5
  let wva: term a
  let wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( a ->4 b )

  proof
    wva
    wva
    wvb
    wva
    comid
    ulemc3.1
    u4lemc2
end
