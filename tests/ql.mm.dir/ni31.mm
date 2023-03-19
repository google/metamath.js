include "wi3.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i3.mm"
include "oran.mm"
include "anor2.mm"
include "con2.mm"
include "ax-r1.mm"
include "2an.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "df-a.mm"
include "anor1.mm"
include "lor.mm"

theorem ni31
  param wva: term a
  param wvb: term b


  assert |- ( a ->3 b ) ' = ( ( ( a v b ' ) ^ ( a v b ) ) ^ ( a ' v ( a ^ b ' ) ) )

  proof
    wva
    wvb
    wi3
    #
    wva
    wvb
    wn
    #
    wo
    #
    wva
    wvb
    wo
    #
    wa
    #
    wva
    wn
    #
    wva
    @1
    wa
    #
    wo
    #
    wa
    #
    @0
    @5
    wvb
    wa
    #
    @5
    @1
    wa
    #
    wo
    #
    wva
    @5
    wvb
    wo
    #
    wa
    #
    wo
    #
    @8
    wn
    #
    wva
    wvb
    df-i3
    @14
    @11
    wn
    #
    @13
    wn
    #
    wa
    #
    wn
    @15
    @11
    @13
    oran
    @18
    @8
    @16
    @4
    @17
    @7
    @11
    @4
    @11
    @9
    wn
    #
    @10
    wn
    #
    wa
    #
    wn
    @4
    wn
    @9
    @10
    oran
    @21
    @4
    @19
    @2
    @20
    @3
    @9
    @2
    wva
    wvb
    anor2
    con2
    @3
    @20
    wva
    wvb
    oran
    ax-r1
    2an
    ax-r4
    ax-r2
    con2
    @13
    @7
    @13
    @5
    @12
    wn
    #
    wo
    #
    wn
    @7
    wn
    wva
    @12
    df-a
    @23
    @7
    @22
    @6
    @5
    @6
    @22
    wva
    wvb
    anor1
    ax-r1
    lor
    ax-r4
    ax-r2
    con2
    2an
    ax-r4
    ax-r2
    ax-r2
    con2
end
