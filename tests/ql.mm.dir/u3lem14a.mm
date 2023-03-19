include "wn.mm"
include "wi3.mm"
include "wi1.mm"
include "u3lem13b.mm"
include "ud3lem0a.mm"
include "wa.mm"
include "wo.mm"
include "df-i3.mm"
include "ancom.mm"
include "u1lemanb.mm"
include "ax-r2.mm"
include "u1lemnanb.mm"
include "2or.mm"
include "ax-a2.mm"
include "wt.mm"
include "u1lemonb.mm"
include "lan.mm"
include "an1.mm"
include "u3lem3.mm"
include "ax-r1.mm"
include "id.mm"

theorem u3lem14a
  let wva: term a
  let wvb: term b


  assert |- ( a ->3 ( ( b ->3 a ' ) ->3 b ' ) ) = ( a ->3 ( b ->3 a ) )

  proof
    wva
    wvb
    wva
    wn
    #
    wi3
    wvb
    wn
    #
    wi3
    #
    wi3
    wva
    wvb
    wva
    wi1
    #
    wi3
    #
    wva
    wvb
    wva
    wi3
    wi3
    #
    @2
    @3
    wva
    wvb
    wva
    u3lem13b
    ud3lem0a
    @4
    @0
    @3
    wa
    #
    @0
    @3
    wn
    #
    wa
    #
    wo
    #
    wva
    @0
    @3
    wo
    #
    wa
    #
    wo
    #
    @5
    wva
    @3
    df-i3
    @12
    @0
    wvb
    wa
    #
    @0
    @1
    wa
    #
    wo
    #
    wva
    wo
    #
    @5
    @9
    @15
    @11
    wva
    @9
    @1
    @0
    wa
    #
    wvb
    @0
    wa
    #
    wo
    #
    @15
    @6
    @17
    @8
    @18
    @6
    @3
    @0
    wa
    @17
    @0
    @3
    ancom
    wvb
    wva
    u1lemanb
    ax-r2
    @8
    @7
    @0
    wa
    @18
    @0
    @7
    ancom
    wvb
    wva
    u1lemnanb
    ax-r2
    2or
    @19
    @18
    @17
    wo
    @15
    @17
    @18
    ax-a2
    @18
    @13
    @17
    @14
    wvb
    @0
    ancom
    @1
    @0
    ancom
    2or
    ax-r2
    ax-r2
    @11
    wva
    wt
    wa
    wva
    @10
    wt
    wva
    @10
    @3
    @0
    wo
    wt
    @0
    @3
    ax-a2
    wvb
    wva
    u1lemonb
    ax-r2
    lan
    wva
    an1
    ax-r2
    2or
    @16
    wva
    @15
    wo
    #
    @5
    @15
    wva
    ax-a2
    @20
    @5
    @5
    @5
    @20
    wva
    wvb
    u3lem3
    ax-r1
    @5
    id
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
