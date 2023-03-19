include "comid.mm"
include "u2lemc2.mm"

theorem u2lemc5
  param wva: term a
  param wvb: term b
  assume ulemc3.1: |- a C b


  assert |- a C ( a ->2 b )

  proof
    wva
    wva
    wvb
    wva
    comid
    ulemc3.1
    u2lemc2
end
