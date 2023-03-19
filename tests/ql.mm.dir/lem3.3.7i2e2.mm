include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wid2.mm"
include "oran3.mm"
include "ax-r1.mm"
include "lor.mm"
include "ran.mm"
include "ax-a3.mm"
include "wt.mm"
include "df-t.mm"
include "ax-r5.mm"
include "or1r.mm"
include "an1r.mm"
include "anor3.mm"
include "orabs.mm"
include "ax-r4.mm"
include "an1.mm"
include "lan.mm"
include "ax-r2.mm"
include "lea.mm"
include "df-le2.mm"
include "3tr.mm"
include "df-id2.mm"
include "3tr1.mm"

theorem lem3.3.7i2e2
  param wva: term a
  param wvb: term b


  assert |- ( a ==2 ( a ^ b ) ) = ( ( a ^ b ) ==2 a )

  proof
    wva
    wva
    wvb
    wa
    #
    wn
    #
    wo
    #
    @0
    wva
    wn
    #
    @1
    wa
    #
    wo
    #
    wa
    #
    @0
    @3
    wo
    #
    wva
    @1
    @3
    wa
    #
    wo
    #
    wa
    #
    wva
    @0
    wid2
    @0
    wva
    wid2
    @6
    wva
    @3
    wvb
    wn
    #
    wo
    #
    wo
    #
    @5
    wa
    wva
    @3
    wo
    #
    @11
    wo
    #
    @5
    wa
    #
    @10
    @2
    @13
    @5
    @1
    @12
    wva
    @12
    @1
    wva
    wvb
    oran3
    ax-r1
    lor
    ran
    @13
    @15
    @5
    @15
    @13
    wva
    @3
    @11
    ax-a3
    ax-r1
    ran
    @16
    wt
    @11
    wo
    #
    @5
    wa
    wt
    @5
    wa
    #
    @10
    @15
    @17
    @5
    @14
    wt
    @11
    wt
    @14
    wva
    df-t
    #
    ax-r1
    ax-r5
    ran
    @17
    wt
    @5
    @11
    or1r
    ran
    @18
    @5
    @0
    wva
    @0
    wo
    #
    wn
    #
    wo
    #
    @10
    @5
    an1r
    @4
    @21
    @0
    wva
    @0
    anor3
    lor
    @22
    @7
    @10
    @21
    @3
    @0
    @20
    wva
    wva
    wvb
    orabs
    ax-r4
    lor
    @7
    @7
    @14
    wa
    #
    @7
    wva
    @0
    wva
    wo
    #
    wn
    #
    wo
    #
    wa
    @10
    @7
    @7
    wt
    wa
    #
    @23
    @27
    @7
    @7
    an1
    ax-r1
    wt
    @14
    @7
    @19
    lan
    ax-r2
    @14
    @26
    @7
    @3
    @25
    wva
    wva
    @24
    @24
    wva
    @0
    wva
    wva
    wvb
    lea
    df-le2
    ax-r1
    ax-r4
    lor
    lan
    @26
    @9
    @7
    @25
    @8
    wva
    @8
    @25
    @0
    wva
    anor3
    ax-r1
    lor
    lan
    3tr
    ax-r2
    3tr
    3tr
    3tr
    wva
    @0
    df-id2
    @0
    wva
    df-id2
    3tr1
end
