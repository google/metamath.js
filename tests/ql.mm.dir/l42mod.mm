include "wo.mm"
include "wa.mm"
include "l42modlem2.mm"
include "l42modlem1.mm"
include "lbtr.mm"

theorem l42mod
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e


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
