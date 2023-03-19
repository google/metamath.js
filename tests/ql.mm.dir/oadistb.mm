include "wi2.mm"
include "wa.mm"
include "wo.mm"
include "df2le2.mm"
include "ran.mm"
include "ax-r1.mm"
include "anass.mm"
include "oagen1.mm"
include "lan.mm"
include "ax-r2.mm"
include "leor.mm"
include "bltr.mm"
include "ledi.mm"
include "lebi.mm"

theorem oadistb
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  let wve: term e
  assume oadistb.2: |- d =< ( a ->2 b )
  assume oadistb.1: |- e =< ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )


  assert |- ( d ^ ( e v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = ( ( d ^ e ) v ( d ^ ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )

  proof
    wvd
    wve
    wva
    wvb
    wi2
    #
    wva
    wvc
    wi2
    wa
    #
    wo
    #
    wa
    #
    wvd
    wve
    wa
    #
    wvd
    @1
    wa
    #
    wo
    #
    @3
    @5
    @6
    @3
    wvd
    @0
    wa
    #
    @2
    wa
    #
    @5
    @8
    @3
    @7
    wvd
    @2
    wvd
    @0
    oadistb.2
    df2le2
    ran
    ax-r1
    @8
    wvd
    @0
    @2
    wa
    #
    wa
    @5
    wvd
    @0
    @2
    anass
    @9
    @1
    wvd
    wva
    wvb
    wvc
    wve
    oadistb.1
    oagen1
    lan
    ax-r2
    ax-r2
    @5
    @4
    leor
    bltr
    wvd
    wve
    @1
    ledi
    lebi
end
