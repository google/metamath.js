include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi0.mm"
include "wid0.mm"
include "wt.mm"
include "or1.mm"
include "ax-r1.mm"
include "lan.mm"
include "an1.mm"
include "df-t.mm"
include "lor.mm"
include "3tr2.mm"
include "ax-a2.mm"
include "ax-a3.mm"
include "3tr.mm"
include "ax-r5.mm"
include "oran3.mm"
include "df-i0.mm"
include "df-id0.mm"
include "3tr1.mm"

theorem lem3.3.7i0e1
  param wva: term a
  param wvb: term b


  assert |- ( a ->0 ( a ^ b ) ) = ( a ==0 ( a ^ b ) )

  proof
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    @2
    @1
    wn
    #
    wva
    wo
    #
    wa
    #
    wva
    @1
    wi0
    wva
    @1
    wid0
    @2
    @2
    wvb
    wn
    #
    @0
    wo
    #
    wva
    wo
    #
    wa
    #
    @2
    @0
    @6
    wo
    #
    wva
    wo
    #
    wa
    @5
    @2
    @2
    @6
    wva
    @0
    wo
    #
    wo
    #
    wa
    #
    @2
    @6
    @0
    wva
    wo
    #
    wo
    #
    wa
    @9
    @2
    wt
    wa
    @2
    @6
    wt
    wo
    #
    wa
    @2
    @14
    wt
    @17
    @2
    @17
    wt
    @6
    or1
    ax-r1
    lan
    @2
    an1
    @17
    @13
    @2
    wt
    @12
    @6
    wva
    df-t
    lor
    lan
    3tr2
    @13
    @16
    @2
    @12
    @15
    @6
    wva
    @0
    ax-a2
    lor
    lan
    @16
    @8
    @2
    @8
    @16
    @6
    @0
    wva
    ax-a3
    ax-r1
    lan
    3tr
    @8
    @11
    @2
    @7
    @10
    wva
    @6
    @0
    ax-a2
    ax-r5
    lan
    @11
    @4
    @2
    @10
    @3
    wva
    wva
    wvb
    oran3
    ax-r5
    lan
    3tr
    wva
    @1
    df-i0
    wva
    @1
    df-id0
    3tr1
end
