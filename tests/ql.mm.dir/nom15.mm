include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "wi1.mm"
include "anass.mm"
include "ax-r1.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "ax-a2.mm"
include "lear.mm"
include "df-le2.mm"
include "3tr.mm"
include "oran3.mm"
include "lan.mm"
include "anabs.mm"
include "2or.mm"
include "df-i5.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom15
  let wva: term a
  let wvb: term b


  assert |- ( a ->5 ( a ^ b ) ) = ( a ->1 b )

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
    wa
    #
    wo
    #
    @2
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
    wi5
    wva
    wvb
    wi1
    @7
    @0
    @2
    wo
    @8
    @4
    @0
    @6
    @2
    @4
    @0
    @3
    wo
    @3
    @0
    wo
    @0
    @1
    @0
    @3
    @1
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @0
    @10
    @1
    wva
    wva
    wvb
    anass
    ax-r1
    @9
    wva
    wvb
    wva
    anidm
    ran
    ax-r2
    ax-r5
    @0
    @3
    ax-a2
    @3
    @0
    @2
    @0
    lear
    df-le2
    3tr
    @6
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
    @13
    @6
    @12
    @5
    @2
    wva
    wvb
    oran3
    lan
    ax-r1
    @2
    @11
    anabs
    ax-r2
    2or
    @0
    @2
    ax-a2
    ax-r2
    wva
    @0
    df-i5
    wva
    wvb
    df-i1
    3tr1
end
