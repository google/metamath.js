include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ancom.mm"
include "lelor.mm"
include "lelan.mm"
include "oal2.mm"
include "letr.mm"
include "df2le2.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "bltr.mm"
include "ledior.mm"
include "ax-a2.mm"
include "lea.mm"
include "df-le2.mm"
include "ran.mm"
include "lbtr.mm"
include "lebi.mm"

theorem oadistc0
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d
  assume oadistc0.1: |- d =< ( ( a ->2 b ) ^ ( a ->2 c ) )
  assume oadistc0.2: |- ( ( a ->2 c ) ^ ( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) ) =< ( ( ( a ->2 b ) ^ ( b v c ) ' ) v d )


  assert |- ( ( a ->2 b ) ^ ( ( b v c ) ' v d ) ) = ( ( ( a ->2 b ) ^ ( b v c ) ' ) v d )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wvc
    wo
    wn
    #
    wvd
    wo
    #
    wa
    #
    @0
    @1
    wa
    wvd
    wo
    #
    @3
    wva
    wvc
    wi2
    #
    @3
    wa
    #
    @4
    @6
    @3
    @6
    @3
    @5
    wa
    @3
    @5
    @3
    ancom
    @3
    @5
    @3
    @0
    @1
    @0
    @5
    wa
    #
    wo
    #
    wa
    @5
    @2
    @8
    @0
    wvd
    @7
    @1
    oadistc0.1
    lelor
    lelan
    wva
    wvb
    wvc
    oal2
    letr
    df2le2
    ax-r2
    ax-r1
    oadistc0.2
    bltr
    @4
    @0
    wvd
    wo
    #
    @2
    wa
    @3
    wvd
    @0
    @1
    ledior
    @9
    @0
    @2
    @9
    wvd
    @0
    wo
    @0
    @0
    wvd
    ax-a2
    wvd
    @0
    wvd
    @7
    @0
    oadistc0.1
    @0
    @5
    lea
    letr
    df-le2
    ax-r2
    ran
    lbtr
    lebi
end
