include "wn.mm"
include "wi3.mm"
include "wo.mm"
include "wa.mm"
include "lear.mm"
include "ax-a1.mm"
include "ax-r1.mm"
include "lbtr.mm"
include "lelor.mm"
include "letr.mm"
include "ud3lem0c.mm"
include "u3lem5.mm"
include "le3tr1.mm"
include "u3lemle1.mm"

theorem u3lem14mp
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->3 b ' ) ' ->3 ( a ->3 ( a ->3 b ) ) ) = 1

  proof
    wva
    wvb
    wn
    #
    wi3
    wn
    #
    wva
    wva
    wvb
    wi3
    wi3
    #
    wva
    @0
    wn
    #
    wo
    wva
    @0
    wo
    wa
    #
    wva
    wn
    #
    wva
    @3
    wa
    #
    wo
    #
    wa
    #
    @5
    wvb
    wo
    #
    @1
    @2
    @8
    @7
    @9
    @4
    @7
    lear
    @6
    wvb
    @5
    @6
    @3
    wvb
    wva
    @3
    lear
    wvb
    @3
    wvb
    ax-a1
    ax-r1
    lbtr
    lelor
    letr
    wva
    @0
    ud3lem0c
    wva
    wvb
    u3lem5
    le3tr1
    u3lemle1
end
