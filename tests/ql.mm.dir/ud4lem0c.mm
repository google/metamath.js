include "wi4.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i4.mm"
include "oran.mm"
include "df-a.mm"
include "con2.mm"
include "anor2.mm"
include "2an.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "anor1.mm"
include "ax-r1.mm"
include "ax-r5.mm"

theorem ud4lem0c
  param wva: term a
  param wvb: term b


  assert |- ( a ->4 b ) ' = ( ( ( a ' v b ' ) ^ ( a v b ' ) ) ^ ( ( a ^ b ' ) v b ) )

  proof
    wva
    wvb
    wi4
    #
    wva
    wn
    #
    wvb
    wn
    #
    wo
    #
    wva
    @2
    wo
    #
    wa
    #
    wva
    @2
    wa
    #
    wvb
    wo
    #
    wa
    #
    @0
    wva
    wvb
    wa
    #
    @1
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wo
    #
    @2
    wa
    #
    wo
    #
    @8
    wn
    #
    wva
    wvb
    df-i4
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
    @5
    @17
    @7
    @11
    @5
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
    @5
    wn
    @9
    @10
    oran
    @21
    @5
    @19
    @3
    @20
    @4
    @9
    @3
    wva
    wvb
    df-a
    con2
    @10
    @4
    wva
    wvb
    anor2
    con2
    2an
    ax-r4
    ax-r2
    con2
    @13
    @7
    @13
    @12
    wn
    #
    wvb
    wo
    #
    wn
    @7
    wn
    @12
    wvb
    anor1
    @23
    @7
    @22
    @6
    wvb
    @6
    @22
    wva
    wvb
    anor1
    ax-r1
    ax-r5
    ax-r4
    ax-r2
    con2
    2an
    ax-r4
    ax-r2
    ax-r2
    con2
end
