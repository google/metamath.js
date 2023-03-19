include "wn.mm"
include "wi2.mm"
include "wo.mm"
include "wa.mm"
include "u2lem7.mm"
include "ax-a2.mm"
include "anor3.mm"
include "anor1.mm"
include "2or.mm"
include "ax-r2.mm"
include "oran3.mm"
include "ax-r5.mm"
include "oran2.mm"
include "con2.mm"

theorem u2lem7n
  let wva: term a
  let wvb: term b


  assert |- ( a ->2 ( a ' ->2 b ) ) ' = ( ( ( a v b ) ^ ( a ' v b ) ) ^ b ' )

  proof
    wva
    wva
    wn
    #
    wvb
    wi2
    wi2
    #
    wva
    wvb
    wo
    #
    @0
    wvb
    wo
    #
    wa
    #
    wvb
    wn
    #
    wa
    #
    @1
    wva
    @5
    wa
    #
    @0
    @5
    wa
    #
    wo
    #
    wvb
    wo
    #
    @6
    wn
    #
    wva
    wvb
    u2lem7
    @10
    @4
    wn
    #
    wvb
    wo
    @11
    @9
    @12
    wvb
    @9
    @2
    wn
    #
    @3
    wn
    #
    wo
    #
    @12
    @9
    @8
    @7
    wo
    @15
    @7
    @8
    ax-a2
    @8
    @13
    @7
    @14
    wva
    wvb
    anor3
    wva
    wvb
    anor1
    2or
    ax-r2
    @2
    @3
    oran3
    ax-r2
    ax-r5
    @4
    wvb
    oran2
    ax-r2
    ax-r2
    con2
end
