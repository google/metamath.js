include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wi2.mm"
include "leor.mm"
include "ax-a1.mm"
include "lbtr.mm"
include "ler2an.mm"
include "lelor.mm"
include "ax-a2.mm"
include "df-i2.mm"
include "le3tr1.mm"

theorem oa4lem2
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oa4lem1.1: |- a =< b '
  assume oa4lem1.2: |- c =< d '


  assert |- ( c v d ) =< ( ( a v c ) ' ->2 d )

  proof
    wvd
    wvc
    wo
    wvd
    wva
    wvc
    wo
    #
    wn
    #
    wn
    #
    wvd
    wn
    #
    wa
    #
    wo
    wvc
    wvd
    wo
    @1
    wvd
    wi2
    wvc
    @4
    wvd
    wvc
    @2
    @3
    wvc
    @0
    @2
    wvc
    wva
    leor
    @0
    ax-a1
    lbtr
    oa4lem1.2
    ler2an
    lelor
    wvc
    wvd
    ax-a2
    @1
    wvd
    df-i2
    le3tr1
end
