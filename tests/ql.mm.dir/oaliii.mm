include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "anass.mm"
include "anidm.mm"
include "lan.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "oal2.mm"
include "leran.mm"
include "bltr.mm"
include "ax-a2.mm"
include "ax-r4.mm"
include "ancom.mm"
include "2or.mm"
include "ran.mm"
include "lebi.mm"

theorem oaliii
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a ->2 b ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) = ( ( a ->2 c ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wvc
    wo
    #
    wn
    #
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
    #
    @3
    @5
    wa
    #
    @6
    @6
    @5
    wa
    #
    @7
    @8
    @6
    @8
    @0
    @5
    @5
    wa
    #
    wa
    @6
    @0
    @5
    @5
    anass
    @9
    @5
    @0
    @5
    anidm
    #
    lan
    ax-r2
    ax-r1
    @6
    @3
    @5
    wva
    wvb
    wvc
    oal2
    leran
    bltr
    @7
    @3
    wvc
    wvb
    wo
    #
    wn
    #
    @3
    @0
    wa
    #
    wo
    #
    wa
    #
    @5
    wa
    #
    @6
    @16
    @7
    @16
    @3
    @14
    @5
    wa
    #
    wa
    @7
    @3
    @14
    @5
    anass
    @17
    @5
    @3
    @17
    @9
    @5
    @14
    @5
    @5
    @12
    @2
    @13
    @4
    @11
    @1
    wvc
    wvb
    ax-a2
    ax-r4
    @3
    @0
    ancom
    2or
    ran
    @10
    ax-r2
    lan
    ax-r2
    ax-r1
    @15
    @0
    @5
    wva
    wvc
    wvb
    oal2
    leran
    bltr
    lebi
end
