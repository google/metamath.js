include "wi3.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "u3lemoa.mm"
include "ax-a2.mm"
include "anor3.mm"
include "anor2.mm"
include "2or.mm"
include "oran3.mm"
include "ax-r2.mm"
include "lor.mm"
include "oran.mm"
include "oran1.mm"
include "3tr2.mm"
include "con1.mm"

theorem u3lemnana
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->3 b ) ' ^ a ' ) = ( a ' ^ ( ( a v b ) ^ ( a v b ' ) ) )

  proof
    wva
    wvb
    wi3
    #
    wn
    wva
    wn
    #
    wa
    #
    @1
    wva
    wvb
    wo
    #
    wva
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
    wva
    wo
    #
    wva
    @6
    wn
    #
    wo
    #
    @2
    wn
    @7
    wn
    @8
    wva
    @1
    wvb
    wa
    #
    @1
    @4
    wa
    #
    wo
    #
    wo
    @10
    wva
    wvb
    u3lemoa
    @13
    @9
    wva
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
    anor3
    wva
    wvb
    anor2
    2or
    @3
    @5
    oran3
    ax-r2
    ax-r2
    lor
    ax-r2
    @0
    wva
    oran
    wva
    @6
    oran1
    3tr2
    con1
end
