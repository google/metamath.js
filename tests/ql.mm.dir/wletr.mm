include "wa.mm"
include "wo.mm"
include "wdf-le2.mm"
include "wr5-2v.mm"
include "wr1.mm"
include "ax-a3.mm"
include "bi1.mm"
include "w3tr2.mm"
include "wlan.mm"
include "anabs.mm"
include "wr2.mm"
include "wdf2le1.mm"

theorem wletr
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wletr.1: |- ( a =<2 b ) = 1
  assume wletr.2: |- ( b =<2 c ) = 1


  assert |- ( a =<2 c ) = 1

  proof
    wva
    wvc
    wva
    wvc
    wa
    wva
    wva
    wvb
    wvc
    wo
    #
    wo
    #
    wa
    #
    wva
    wvc
    @1
    wva
    @0
    wva
    wvb
    wo
    #
    wvc
    wo
    #
    wvc
    @1
    @4
    @0
    @3
    wvb
    wvc
    wva
    wvb
    wletr.1
    wdf-le2
    wr5-2v
    wr1
    wvb
    wvc
    wletr.2
    wdf-le2
    @4
    @1
    wva
    wvb
    wvc
    ax-a3
    bi1
    w3tr2
    wlan
    @2
    wva
    wva
    @0
    anabs
    bi1
    wr2
    wdf2le1
end
