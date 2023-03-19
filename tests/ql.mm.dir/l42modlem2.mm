include "wo.mm"
include "wa.mm"
include "lea.mm"
include "leror.mm"
include "leor.mm"
include "le2an.mm"

theorem l42modlem2
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e


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
