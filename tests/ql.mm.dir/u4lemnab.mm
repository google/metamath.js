include "wi4.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "u4lemonb.mm"
include "ax-a2.mm"
include "anor2.mm"
include "df-a.mm"
include "2or.mm"
include "oran3.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "oran1.mm"
include "3tr2.mm"
include "con1.mm"

theorem u4lemnab
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->4 b ) ' ^ b ) = ( ( ( a v b ' ) ^ ( a ' v b ' ) ) ^ b )

  proof
    wva
    wvb
    wi4
    #
    wn
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wo
    #
    wva
    wn
    #
    @2
    wo
    #
    wa
    #
    wvb
    wa
    #
    @0
    @2
    wo
    #
    @6
    wn
    #
    @2
    wo
    #
    @1
    wn
    @7
    wn
    @8
    wva
    wvb
    wa
    #
    @4
    wvb
    wa
    #
    wo
    #
    @2
    wo
    @10
    wva
    wvb
    u4lemonb
    @13
    @9
    @2
    @13
    @12
    @11
    wo
    #
    @9
    @11
    @12
    ax-a2
    @14
    @3
    wn
    #
    @5
    wn
    #
    wo
    @9
    @12
    @15
    @11
    @16
    wva
    wvb
    anor2
    wva
    wvb
    df-a
    2or
    @3
    @5
    oran3
    ax-r2
    ax-r2
    ax-r5
    ax-r2
    @0
    wvb
    oran1
    @6
    wvb
    oran3
    3tr2
    con1
end
