include "comid.mm"
include "u1lemc2.mm"

theorem u1lemc3
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( b ->1 a )

  proof
    wva
    wvb
    wva
    ulemc3.1
    wva
    comid
    u1lemc2
end
