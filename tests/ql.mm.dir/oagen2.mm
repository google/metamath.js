include "wi2.mm"
include "wa.mm"
include "wo.mm"
include "wn.mm"
include "wi0.mm"
include "df-i0.mm"
include "lbtr.mm"
include "lelan.mm"
include "oal2.mm"
include "letr.mm"

theorem oagen2
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oagen2.1: |- d =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )


  assert |- ( ( a ->2 b ) ^ d ) =< ( a ->2 c )

  proof
    wva
    wvb
    wi2
    #
    wvd
    wa
    @0
    wvb
    wvc
    wo
    #
    wn
    @0
    wva
    wvc
    wi2
    #
    wa
    #
    wo
    #
    wa
    @2
    wvd
    @4
    @0
    wvd
    @1
    @3
    wi0
    @4
    oagen2.1
    @1
    @3
    df-i0
    lbtr
    lelan
    wva
    wvb
    wvc
    oal2
    letr
end
