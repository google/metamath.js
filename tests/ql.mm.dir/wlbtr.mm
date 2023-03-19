include "wa.mm"
include "wr1.mm"
include "wlan.mm"
include "wdf2le2.mm"
include "wr2.mm"
include "wdf2le1.mm"

theorem wlbtr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wlbtr.1: |- ( a =<2 b ) = 1
  assume wlbtr.2: |- ( b == c ) = 1


  assert |- ( a =<2 c ) = 1

  proof
    wva
    wvc
    wva
    wvc
    wa
    wva
    wvb
    wa
    wva
    wvc
    wvb
    wva
    wvb
    wvc
    wlbtr.2
    wr1
    wlan
    wva
    wvb
    wlbtr.1
    wdf2le2
    wr2
    wdf2le1
end
