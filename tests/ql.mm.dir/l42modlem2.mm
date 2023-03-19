include "wo.mm"
include "wa.mm"
include "lea.mm"
include "leror.mm"
include "leor.mm"
include "le2an.mm"

theorem l42modlem2
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  param wve: term e


  assert |- ( ( ( ( a v b ) ^ c ) v d ) ^ e ) =< ( ( ( a v b ) v d ) ^ ( ( a v b ) v e ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wa
    #
    wvd
    wo
    @0
    wvd
    wo
    wve
    @0
    wve
    wo
    @1
    @0
    wvd
    @0
    wvc
    lea
    leror
    wve
    @0
    leor
    le2an
end
