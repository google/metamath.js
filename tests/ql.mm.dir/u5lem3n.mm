include "wi5.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "u5lem3.mm"
include "ax-a2.mm"
include "anor1.mm"
include "df-a.mm"
include "2or.mm"
include "oran3.mm"
include "ax-r2.mm"
include "lor.mm"
include "con2.mm"

theorem u5lem3n
  let wva: term a
  let wvb: term b


  assert |- ( a ->5 ( b ->5 a ) ) ' = ( a ^ ( ( a ' v b ) ^ ( a ' v b ' ) ) )

  proof
    wva
    wvb
    wva
    wi5
    wi5
    #
    wva
    wva
    wn
    #
    wvb
    wo
    #
    @1
    wvb
    wn
    #
    wo
    #
    wa
    #
    wa
    #
    @0
    @1
    wva
    wvb
    wa
    #
    wva
    @3
    wa
    #
    wo
    #
    wo
    #
    @6
    wn
    #
    wva
    wvb
    u5lem3
    @10
    @1
    @5
    wn
    #
    wo
    @11
    @9
    @12
    @1
    @9
    @8
    @7
    wo
    #
    @12
    @7
    @8
    ax-a2
    @13
    @2
    wn
    #
    @4
    wn
    #
    wo
    @12
    @8
    @14
    @7
    @15
    wva
    wvb
    anor1
    wva
    wvb
    df-a
    2or
    @2
    @4
    oran3
    ax-r2
    ax-r2
    lor
    wva
    @5
    oran3
    ax-r2
    ax-r2
    con2
end
