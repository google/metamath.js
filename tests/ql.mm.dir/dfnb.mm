include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "oran.mm"
include "con2.mm"
include "ancom.mm"
include "ax-r2.mm"
include "dfb.mm"
include "ax-r4.mm"
include "df-a.mm"
include "ax-r1.mm"
include "2an.mm"
include "3tr1.mm"

theorem dfnb
  param wva: term a
  param wvb: term b


  assert |- ( a == b ) ' = ( ( a v b ) ^ ( a ' v b ' ) )

  proof
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wn
    #
    @3
    wn
    #
    @0
    wn
    #
    wa
    #
    wva
    wvb
    tb
    #
    wn
    wva
    wvb
    wo
    #
    @1
    @2
    wo
    #
    wa
    @5
    @7
    @6
    wa
    #
    @8
    @4
    @12
    @0
    @3
    oran
    con2
    @7
    @6
    ancom
    ax-r2
    @9
    @4
    wva
    wvb
    dfb
    ax-r4
    @10
    @6
    @11
    @7
    wva
    wvb
    oran
    @7
    @11
    @0
    @11
    wva
    wvb
    df-a
    con2
    ax-r1
    2an
    3tr1
end
