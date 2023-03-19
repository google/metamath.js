include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "wi1.mm"
include "anass.mm"
include "ax-r1.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r2.mm"
include "oran3.mm"
include "lan.mm"
include "anabs.mm"
include "2or.mm"
include "ax-a2.mm"
include "dfb.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom25
  let wva: term a
  let wvb: term b


  assert |- ( a == ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wva
    wvb
    wa
    #
    wa
    #
    wva
    wn
    #
    @0
    wn
    #
    wa
    #
    wo
    #
    @2
    @0
    wo
    #
    wva
    @0
    tb
    wva
    wvb
    wi1
    @5
    @0
    @2
    wo
    @6
    @1
    @0
    @4
    @2
    @1
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @0
    @8
    @1
    wva
    wva
    wvb
    anass
    ax-r1
    @7
    wva
    wvb
    wva
    anidm
    ran
    ax-r2
    @4
    @2
    @2
    wvb
    wn
    #
    wo
    #
    wa
    #
    @2
    @11
    @4
    @10
    @3
    @2
    wva
    wvb
    oran3
    lan
    ax-r1
    @2
    @9
    anabs
    ax-r2
    2or
    @0
    @2
    ax-a2
    ax-r2
    wva
    @0
    dfb
    wva
    wvb
    df-i1
    3tr1
end
