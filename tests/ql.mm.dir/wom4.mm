include "wn.mm"
include "wo.mm"
include "wa.mm"
include "woml.mm"
include "wdf-le2.mm"
include "wlan.mm"
include "wlor.mm"
include "w3tr2.mm"

theorem wom4
  param wva: term a
  param wvb: term b
  assume wom4.1: |- ( a =<2 b ) = 1


  assert |- ( ( a v ( a ' ^ b ) ) == b ) = 1

  proof
    wva
    wva
    wn
    #
    wva
    wvb
    wo
    #
    wa
    #
    wo
    @1
    wva
    @0
    wvb
    wa
    #
    wo
    wvb
    wva
    wvb
    woml
    @2
    @3
    wva
    @1
    wvb
    @0
    wva
    wvb
    wom4.1
    wdf-le2
    #
    wlan
    wlor
    @4
    w3tr2
end
