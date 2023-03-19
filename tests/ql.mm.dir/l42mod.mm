include "wo.mm"
include "wa.mm"
include "l42modlem2.mm"
include "l42modlem1.mm"
include "lbtr.mm"

theorem l42mod
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e


  assert |- ( ( ( ( a v b ) ^ c ) v d ) ^ e ) =< ( ( a v b ) v ( ( a v d ) ^ ( b v e ) ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wa
    wvd
    wo
    wve
    wa
    @0
    wvd
    wo
    @0
    wve
    wo
    wa
    @0
    wva
    wvd
    wo
    wvb
    wve
    wo
    wa
    wo
    wva
    wvb
    wvc
    wvd
    wve
    l42modlem2
    wva
    wvb
    wvd
    wve
    l42modlem1
    lbtr
end
