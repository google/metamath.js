include "tb.mm"
include "ublemc1.mm"
include "bicom.mm"
include "cbtr.mm"

theorem ublemc2
  param wva: term a
  param wvb: term b


  assert |- b C ( a == b )

  proof
    wvb
    wvb
    wva
    tb
    wva
    wvb
    tb
    wvb
    wva
    ublemc1
    wvb
    wva
    bicom
    cbtr
end
