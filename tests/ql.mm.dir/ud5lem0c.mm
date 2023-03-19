include "wi5.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i5.mm"
include "oran.mm"
include "df-a.mm"
include "con2.mm"
include "anor2.mm"
include "2an.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "ax-r1.mm"

theorem ud5lem0c
  let wva: term a
  let wvb: term b


  assert |- ( a ->5 b ) ' = ( ( ( a ' v b ' ) ^ ( a v b ' ) ) ^ ( a v b ) )

  proof
    wva
    wvb
    wi5
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
    @2
    wa
    #
    wo
    #
    @7
    wn
    #
    wva
    wvb
    df-i5
    @12
    @10
    wn
    #
    @11
    wn
    #
    wa
    #
    wn
    @13
    @10
    @11
    oran
    @16
    @7
    @14
    @5
    @15
    @6
    @10
    @5
    @10
    @8
    wn
    #
    @9
    wn
    #
    wa
    #
    wn
    @5
    wn
    @8
    @9
    oran
    @19
    @5
    @17
    @3
    @18
    @4
    @8
    @3
    wva
    wvb
    df-a
    con2
    @9
    @4
    wva
    wvb
    anor2
    con2
    2an
    ax-r4
    ax-r2
    con2
    @6
    @15
    wva
    wvb
    oran
    ax-r1
    2an
    ax-r4
    ax-r2
    ax-r2
    con2
end
