include "wi5.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "u5lemob.mm"
include "anor3.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "oran.mm"
include "oran2.mm"
include "3tr2.mm"
include "con1.mm"

theorem u5lemnanb
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->5 b ) ' ^ b ' ) = ( ( a v b ) ^ b ' )

  proof
    wva
    wvb
    wi5
    #
    wn
    wvb
    wn
    #
    wa
    #
    wva
    wvb
    wo
    #
    @1
    wa
    #
    @0
    wvb
    wo
    #
    @3
    wn
    #
    wvb
    wo
    #
    @2
    wn
    @4
    wn
    @5
    wva
    wn
    @1
    wa
    #
    wvb
    wo
    @7
    wva
    wvb
    u5lemob
    @8
    @6
    wvb
    wva
    wvb
    anor3
    ax-r5
    ax-r2
    @0
    wvb
    oran
    @3
    wvb
    oran2
    3tr2
    con1
end
