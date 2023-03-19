include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wid3.mm"
include "wt.mm"
include "anor3.mm"
include "lor.mm"
include "lan.mm"
include "orabs.mm"
include "ax-r4.mm"
include "df-t.mm"
include "ax-r1.mm"
include "an1.mm"
include "ax-a2.mm"
include "3tr.mm"
include "lea.mm"
include "df-le2.mm"
include "an1r.mm"
include "ax-r2.mm"
include "or1.mm"
include "ran.mm"
include "ax-a3.mm"
include "ax-r5.mm"
include "oran3.mm"
include "df-id3.mm"
include "3tr1.mm"

theorem lem3.3.7i3e2
  param wva: term a
  param wvb: term b


  assert |- ( a ==3 ( a ^ b ) ) = ( ( a ^ b ) ==3 a )

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
    wva
    @0
    @1
    wn
    #
    wa
    #
    wo
    #
    wa
    #
    @3
    wva
    wo
    #
    @1
    @3
    @0
    wa
    #
    wo
    #
    wa
    #
    wva
    @1
    wid3
    @1
    wva
    wid3
    @6
    wvb
    wn
    #
    @0
    wo
    #
    wva
    wo
    #
    @9
    wa
    #
    @0
    @11
    wo
    #
    wva
    wo
    #
    @9
    wa
    @10
    @6
    @11
    wva
    @0
    wo
    #
    wo
    #
    @9
    wa
    #
    @11
    @0
    wva
    wo
    #
    wo
    #
    @9
    wa
    @14
    @6
    wt
    @9
    wa
    #
    @11
    wt
    wo
    #
    @9
    wa
    @19
    @6
    @9
    @22
    @6
    @1
    @0
    wo
    #
    @1
    @1
    wva
    wo
    #
    wn
    #
    wo
    @9
    @6
    @2
    wva
    wva
    @1
    wo
    #
    wn
    #
    wo
    #
    wa
    @2
    @17
    wa
    #
    @24
    @5
    @29
    @2
    @4
    @28
    wva
    wva
    @1
    anor3
    lor
    lan
    @29
    @17
    @2
    @28
    @0
    wva
    @27
    wva
    wva
    wvb
    orabs
    ax-r4
    lor
    lan
    @30
    @2
    wt
    wa
    @2
    @24
    @17
    wt
    @2
    wt
    @17
    wva
    df-t
    #
    ax-r1
    lan
    @2
    an1
    @0
    @1
    ax-a2
    3tr
    3tr
    @0
    @26
    @1
    wva
    @25
    @25
    wva
    @1
    wva
    wva
    wvb
    lea
    df-le2
    ax-r1
    ax-r4
    lor
    @26
    @8
    @1
    @8
    @26
    @1
    wva
    anor3
    ax-r1
    lor
    3tr
    @22
    @9
    @9
    an1r
    ax-r1
    ax-r2
    wt
    @23
    @9
    @23
    wt
    @11
    or1
    ax-r1
    ran
    @23
    @18
    @9
    wt
    @17
    @11
    @31
    lor
    ran
    3tr
    @18
    @21
    @9
    @17
    @20
    @11
    wva
    @0
    ax-a2
    lor
    ran
    @21
    @13
    @9
    @13
    @21
    @11
    @0
    wva
    ax-a3
    ax-r1
    ran
    3tr
    @13
    @16
    @9
    @12
    @15
    wva
    @11
    @0
    ax-a2
    ax-r5
    ran
    @16
    @7
    @9
    @15
    @3
    wva
    wva
    wvb
    oran3
    ax-r5
    ran
    3tr
    wva
    @1
    df-id3
    @1
    wva
    df-id3
    3tr1
end
